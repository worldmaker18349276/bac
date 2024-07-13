{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Add (
  addNDSymbol,
  addLeafNode,
  addParentNode,
  addParentNodeOnRoot,
) where

import Control.Monad (guard)
import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.List (findIndex, sort)
import Data.List.Extra (anySame, nubSort, snoc)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.Utils (asserted, (.>), (|>))
import Data.Tuple (swap)
import BAC.Fundamental.Fraction (Cofraction, Fraction, findValidCofractionsFractions,
  compatibleFractions, compatibleCofractionsFractions, compatibleCofractions)

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)
  
{- |
Add a nondecomposable symbol on a node, where the parameters @src :: Symbol@ and @tgt ::
Symbol@ are the symbols of source node and target node of the added edge, and @sym ::
Symbol@ is the symbol to be added.  @src_alts :: [Cofraction]@ is the list of picked
cofractions, and @tgt_alts :: [Fraction]@ is the list of picked fractions.

In categorical perspectives, it adds a non-terminal nondecomposable morphism, where `src`
and `tgt` indicates the source object and target object of the added morphism, and
`(src, sym)` will become the pair of symbol indicating the added morphism.

Cofractions and fraction s represent possible choices of composition rules, and can be
obtained by a helper function `findValidCofractionsFractions`, which returns two groups of
picklists.  The second group contains picklists of fractions, which are used to determine
the outgoing wires.  The first group contains picklists of cofractions, which are used to
determine the incoming wires.  User should select one fraction or cofraction for each
picklist.  A valid choice of fractions and cofractions can be checked by functions
`compatibleFractions`, `compatibleCofractions` and `compatibleCofractionsFractions`.

Examples:

>>> fromJust $ findValidCofractionsFractions 1 6 cone
([[((0,6),(0,1))]],[])
>>> printBAC $ fromJust $ addNDSymbol 1 6 2 () [((0,6),(0,1))] [] cone
[1;2;6;]
  [2;]
    &0
  [1;]
    &1
[3;4;2;6;4;]
  [1;2;3;]
    &2
    [1;]
      *1
    [2;]
      *0
  [4;2;3;]
    *2
-}
addNDSymbol ::
  Monoid e
  => Symbol
  -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol
  -- ^ The symbol indicating the target object of the morphism to be added.
  -> Symbol
  -- ^ The symbol to be added.
  -> e
  -> [Cofraction]
  -- ^ The picked fractions from `findValidCofractionsFractions`.
  -> [Fraction]
  -- ^ The picked fractions from `findValidCofractionsFractions`.
  -> BAC e
  -> Maybe (BAC e)
addNDSymbol src tgt sym e src_alts tgt_alts node = do
  -- ensure that `src` and `tgt` are reachable, and check the order between `src` and `tgt`
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  let src_node = target src_arr
  guard $ locate tgt_arr src |> (== Outer)
  -- ensure that it is valid to add symbol `sym` to the node of `src`
  guard $ src_node |> symbols |> (`snoc` sym) |> anySame |> not

  -- check picked fractions and cofractions
  let (cofractions, fractions) = findValidCofractionsFractions src tgt node |> fromJust
  guard $
    src_alts
    |> traverse (\cofraction -> cofractions |> findIndex (elem cofraction))
    |> maybe False (sort .> (== [0 .. length cofractions - 1]))
  guard $
    tgt_alts
    |> traverse (\fraction -> fractions |> findIndex (elem fraction))
    |> maybe False (sort .> (== [0 .. length fractions - 1]))

  -- ensure that picked fractions and cofractions are compatible
  guard $ compatibleFractions node tgt_alts
  guard $ compatibleCofractionsFractions node src_alts tgt_alts
  guard $ compatibleCofractions node src_alts

  -- construct added edge
  let new_dict =
        -- zip values of dictionaries of the denominator and the numerator
        -- which form wires from node of `tgt` to `src`
        tgt_alts
        |> fmap (both (arrow2 node .> fromJust))
        |> concatMap (both (snd .> dict .> Map.elems) .> swap .> uncurry zip)
        -- make a dictionary
        |> nubSort
        |> asserted (fmap fst .> anySame .> not) -- checked by `compatibleFractions`
        |> Map.fromList
        -- link base symbol to the new symbol `sym`
        |> Map.insert base sym
        |> asserted (Map.keys .> (== symbols (target tgt_arr)))
  let new_edge = Arrow {dict = new_dict, value = e, target = target tgt_arr}

  -- add the new edge to `src_node`
  let src_node' = src_node |> edges |> (new_edge :) |> BAC

  -- find new added wire with start point `sym` on the node of `src`
  -- the parameter is 2-chain representing a proper edge to add a wire
  -- it return a pair of symbols representing the added wire
  let determine_new_wire (arr1, arr23) =
        -- make suffix decomposition on this edge: `arr23` => `(arr2, arr3)`
        suffixND (target arr1) (symbol arr23)
        |> head -- either of these will give the same result, checked by `compatibleCofractions`
        |> \(arr2, arr3) ->
          -- determine new added wire for the nondecomposable edge `arr3` first
          -- find corresponding cofraction
          src_alts
          |> find (snd .> (== symbol2 (arr1 `join` arr2, arr3)))
          |> fromJust
          -- symbol `sym` will be mapped to the symbol referencing the numerator of this cofraction
          |> (\((_, s), _) -> (sym, s))
          -- determine new added wire for the edge `arr23`
          |> second (dict arr2 !)

  -- add new wires to incoming edges of `src_node`
  fromReachable src_node' $ root node |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    -- add new wire for added symbol
    AtBoundary -> return edge {dict = new_dict, target = src_node'}
      where
      new_wire = determine_new_wire (curr, edge)
      new_dict = dict edge |> uncurry Map.insert new_wire

{- |
Add a leaf node to a node, where @src :: Symbol@ indicates the node to be appended, and
@sym :: Symbol@ is the added symbol referencing the added node.
@inserter :: (Symbol, Symbol) -> Symbol@ is the function to insert a symbol to all
ancestor nodes, such that it will reference the added node.  The parameter of `inserter`
is a pair of symbols, indicates the arrow from the node to insert the symbol, to the node
to append.  Inserter can be made by `BAC.Fundamental.makeShifter`.

In categorical perspectives, it adds a terminal nondecomposable morphism, where `src`
indicates an object whose terminal morphism will be interpolated, and @(src, sym)@ will
indicate the only morphism from such object to the inserted object.  For all incoming
morphisms of the object `src`, say @(s1, s2)@, the pair of symbol
@(s1, inserter (s1, s2))@ will indicate the incoming morphism of the inserted object with
the same source object.

Examples:

>>> printBAC $ fromJust $ addLeafNode 2 1 () (makeShifter cone 1) cone
[1;2;8;]
  [1;2;]
    &0
    [1;]
[3;4;2;6;4;8;]
  [1;2;3;6;]
    &1
    [1;3;]
      *0
    [2;]
  [4;2;3;6;]
    *1

>>> printBAC $ fromJust $ addLeafNode 4 3 () (makeShifter cone 1) cone
[1;2;]
  [1;]
    &0
[3;4;2;6;4;10;10;]
  [1;2;3;5;]
    &1
    [3;]
    [1;]
      *0
    [2;]
  [4;2;3;8;]
    *1
-}
addLeafNode ::
  Monoid e
  => Symbol
  -- ^ The symbol referencing the node to append.
  -> Symbol
  -- ^ The symbol referencing the added node.
  -> e
  -> ((Symbol, Symbol) -> Symbol)
  -- ^ The function to insert symbol to all ancestor nodes.
  -> BAC e
  -> Maybe (BAC e)
addLeafNode src sym e inserter node = do
  -- ensure that `src` is reachable
  src_arr <- arrow node src
  let src_node = target src_arr

  -- validate added symbols
  guard $ src_node |> symbols |> (`snoc` sym) |> anySame |> not
  guard $
    arrowsUnder node src |> all \curr ->
      let
        add_list = curr `divide` src_arr |> fmap ((curr,) .> symbol2 .> inserter)
      in
        symbols (target curr) |> (++ add_list) |> anySame |> not

  -- add the new node to `src_node`
  let new_edge = Arrow (Map.singleton base sym) e empty
  let src_node' = src_node |> edges |> (new_edge :) |> BAC

  fromReachable src_node' $
    root node |> modifyUnder src \(curr, edge) -> \case
      AtOuter -> return edge
      AtBoundary -> return edge {dict = new_dict, target = src_node'}
        where
        -- determine new symbol to insert
        new_sym = inserter (symbol curr, symbol edge)
        new_dict = dict edge |> Map.insert sym new_sym
      AtInner subnode -> return edge {dict = new_dict, target = subnode}
        where
        new_wires =
          -- find all arrows from the node of `src` to the target node of this edge
          (curr `join` edge) `divide` src_arr
          |> fmap \subarr ->
            -- the inserted symbol for `subarr` should be wired to the inserted symbol for `join edge subarr`
            ((curr `join` edge, subarr), (curr, edge `join` subarr))
            |> both (symbol2 .> inserter)
        new_dict = dict edge `Map.union` Map.fromList new_wires

{- |
Insert a node in the middle of an arrow, where @(src, tgt) :: (Symbol, Symbol)@ indicates
the arrow to interpolate, @sym :: Symbol@ is the symbol to add, and @mapping :: Dict@ is
the dictionary of the edge of the added node.  @inserter :: (Symbol, Symbol) -> Symbol@
is the function to insert a symbol to all ancestor nodes, such that it will reference the
added node, which is the same as `addLeafNode`.

In categorical perspectives, it adds an object in between a morphism, where @(src, tgt)@
indicates the morphism to be interpolated, and @(src, sym)@ will indicate the incoming
morphism of the added object.

Examples:

>>> import Control.Arrow ((&&&))
>>> mapping = arrow cone 4 |> fromJust |> target |> symbols |> fmap (id &&& (+1)) |> Map.fromList
>>> printBAC $ fromJust $ addParentNode (3,1) 5 mapping ((), ()) (makeShifter cone 1) cone
[1;2;]
  [1;]
    &0
[3;4;2;6;4;9;]
  [5;1;2;3;]
    [1;2;3;]
      &1
      [1;]
        *0
      [2;]
  [1;2;3;]
    *1
  [4;2;3;]
    *1
-}
addParentNode ::
  Monoid e
  => (Symbol, Symbol)  -- ^ The pair of symbols indicating the arrow to be interpolated.
  -> Symbol         -- ^ The symbol referencing the added node.
  -> Dict           -- ^ The dictionary of the edge of the added node.
  -> (e, e)
  -> ((Symbol, Symbol) -> Symbol)
                    -- ^ The function to insert symbol to all ancestor nodes.
  -> BAC e
  -> Maybe (BAC e)
addParentNode (src, tgt) sym mapping (e1, e2) inserter node = do
  -- ensure that `(src, tgt)` is reachable and proper
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let tgt_arr = src_arr `join` tgt_subarr
  guard $ tgt /= base

  -- validate dictionary `mapping`
  guard $ symbols (target tgt_subarr) |> (== Map.keys mapping)
  guard $ Map.elems mapping |> (base :) |> anySame |> not
  -- validate added symbols
  guard $ symbols src_node |> (`snoc` sym) |> anySame |> not
  guard $
    arrowsUnder node src |> all \curr ->
      let
        add_list = curr `divide` tgt_arr |> fmap ((curr,) .> symbol2 .> inserter)
      in
        symbols (target curr) |> (++ add_list) |> anySame |> not

  -- add edge to the node of `src`
  let new_outedge = Arrow {dict = mapping, value = e2, target = target tgt_subarr}
  let new_node = BAC [new_outedge]
  let new_indict = dict tgt_subarr |> Map.mapKeys (mapping !) |> Map.insert base sym
  let new_inedge = Arrow {dict = new_indict, value = e1, target = new_node}
  let src_node' = src_node |> edges |> (new_inedge :) |> BAC

  fromReachable src_node' $
    root node |> modifyUnder src \(curr, edge) -> \case
      AtOuter -> return edge
      AtBoundary -> return edge {dict = new_dict, target = src_node'}
        where
        new_sym = inserter (symbol curr, symbol edge)
        new_dict = dict edge |> Map.insert sym new_sym
      AtInner subnode -> return edge {dict = new_dict, target = subnode}
        where
        new_wires =
          -- find all arrows from the node of `src` to the target node of this edge
          (curr `join` edge) `divide` src_arr
          |> fmap \subarr ->
            -- the inserted symbol for `subarr` should be wired to the inserted symbol for `join edge subarr`
            ((curr `join` edge, subarr), (curr, edge `join` subarr))
            |> both (symbol2 .> inserter)
        new_dict = dict edge `Map.union` Map.fromList new_wires

-- | Insert a node in the middle of an arrow started at the root (add an object).  See
--   `addParentNode` for details.
addParentNodeOnRoot :: Monoid e => Symbol -> Symbol -> Dict -> (e, e) -> BAC e -> Maybe (BAC e)
addParentNodeOnRoot tgt sym mapping (e1, e2) = addParentNode (base, tgt) sym mapping (e1, e2) undefined
