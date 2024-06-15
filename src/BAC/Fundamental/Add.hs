{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Add (
  Cofraction,
  Fraction,
  validateCofraction,
  validateFraction,
  extendCofraction,
  extendFraction,
  compatibleFractions,
  compatibleCofractions,
  compatibleCofractionsFractions,
  findValidCofractionsFractions,
  addNDSymbol,
  addLeafNode,
  addParentNode,
  addParentNodeOnRoot,
) where

import Control.Monad (guard, mzero)
import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.List (findIndex, sort)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, snoc, nubSortOn)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.Utils (asserted, guarded, (.>), (|>))
import Data.Tuple (swap)

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

-- | Two pairs of symbols representing two morphisms with the same starting node.  The
--   first pair of symbols is called numerator; the second pair of symbols is called
--   denominator.
type Cofraction = ((Symbol, Symbol), (Symbol, Symbol))

-- | Two pairs of symbols representing two morphisms with the same ending node. The first
--   pair of symbols is called numerator; the second pair of symbols is called
--   denominator.
type Fraction = ((Symbol, Symbol), (Symbol, Symbol))


-- | Check whether a given value is a valid cofraction.  A valid cofraction obey: coforks
--   of the denominator are also coforks of the numerator.  A cofork of a morphism `f` is
--   a pair of distinct morphisms @(g, g')@ such that @f . g = f . g'@.
validateCofraction :: Monoid e => BAC e -> Cofraction -> Bool
validateCofraction node (n, d) = isJust do
  -- ensure that `n`, `d` are reachable
  n_arr_arr <- arrow2 node n
  d_arr_arr <- arrow2 node d
  -- ensure that `n_arr_arr` and `d_arr_arr` start at the same node
  guard $ symbol (fst n_arr_arr) == symbol (fst d_arr_arr)
  let sym0 = symbol (fst n_arr_arr)

  -- ensure that all coforks of `n` are also coforks of `d`
  guard $
    -- find all nondecomposable incoming edges
    suffixND node sym0
    -- group them to form coforks of `d_arr_arr`
    |> groupSortOn (second (`join` snd d_arr_arr) .> symbol2)
    -- for each group, they should also be cofork of `n_arr_arr`
    |> all (fmap (second (`join` snd n_arr_arr) .> symbol2) .> allSame)

-- | Check whether a given value is a valid fraction.  A valid fraction obey: forks of the
--   denominator are also forks of the numerator.  A fork of a morphism `f` is a pair of
--   distinct morphisms @(g, g')@ such that @g . f = g' . f@.
validateFraction :: Monoid e => BAC e -> Fraction -> Bool
validateFraction node (n, d) = isJust do
  -- ensure that `n`, `d` are reachable
  n_arr_arr <- arrow2 node n
  d_arr_arr <- arrow2 node d
  -- ensure that `n_arr_arr` and `d_arr_arr` end at the same node
  guard $ symbol (uncurry join n_arr_arr) == symbol (uncurry join d_arr_arr)
  let node0 = target (uncurry join n_arr_arr)

  -- ensure that all forks of `n` are also forks of `d`
  guard $
    -- find all nondecomposable outgoing edges
    edgesND node0
    -- group them to form forks of `d`
    |> groupSortOn ((snd d_arr_arr `join`) .> symbol)
    -- for each group, they should also be fork of `n`
    |> all (fmap ((snd n_arr_arr `join`) .> symbol) .> allSame)


-- | Extend a cofraction with an arrow ending at the vertex of this cofraction.
--   An extended valid cofraction is also a valid cofraction.
extendCofraction :: Monoid e => BAC e -> (Symbol, Symbol) -> Cofraction -> Maybe Cofraction
extendCofraction node q (n, d) = do
  -- ensure `q`, `n`, `d` are reachable
  (q_arr, q_subarr) <- arrow2 node q
  (n_arr, n_subarr) <- arrow2 node n
  (d_arr, d_subarr) <- arrow2 node d
  -- ensure `q` and `n`/`d` are composable
  guard $
    symbol n_arr == symbol d_arr
    && symbol n_arr == symbol (q_arr `join` q_subarr)
  -- compose arrow and edges
  let n' = symbol2 (q_arr, q_subarr `join` n_subarr)
  let d' = symbol2 (q_arr, q_subarr `join` d_subarr)
  return (n', d')

-- | Extend a fraction with an arrow starting at the vertex of this fraction.
--   An extended valid fraction is also a valid fraction.
extendFraction :: Monoid e => BAC e -> Fraction -> (Symbol, Symbol) -> Maybe Fraction
extendFraction node (n, d) q = do
  -- ensure `q`, `n`, `d` are reachable
  (q_arr, q_subarr) <- arrow2 node q
  (d_arr, d_subarr) <- arrow2 node d
  (n_arr, n_subarr) <- arrow2 node n
  -- ensure `n`/`d` and `q` are composable
  guard $
    symbol (n_arr `join` n_subarr) == symbol (d_arr `join` d_subarr)
    && symbol q_arr == symbol (d_arr `join` d_subarr)
  -- compose edges and arrow
  let n' = symbol2 (n_arr, n_subarr `join` q_subarr)
  let d' = symbol2 (d_arr, d_subarr `join` q_subarr)
  return (n', d')


-- | Check whether a list of fractions are compatible with each other.
--   Fraction @(n, d)@ and fraction @(n', d')@ are compatible if @q . d = q' . d'@ implies
--   @q . n = q' . n'@ for all `q` and 'q''.  That is, two fractions are compatible if
--   their extensions are unique on the denominator.
--   A valid fraction is compatible with itself.
compatibleFractions :: Monoid e => BAC e -> [Fraction] -> Bool
compatibleFractions node fractions = isJust do
  -- ensure that all denominators/numerators of fractions start at the same node
  guard $ fractions |> fmap (both fst) |> allSame

  pairs <- fractions |> traverse \(n, d) -> do
    n_arr_arr <- arrow2 node n
    d_arr_arr <- arrow2 node d
    -- zip values of dictionaries of the denominator and the numerator
    -- which form pairs between symbols on the starting nodes of those two edges
    let n_syms = n_arr_arr |> snd |> dict |> Map.elems
    let d_syms = d_arr_arr |> snd |> dict |> Map.elems
    return $ n_syms `zip` d_syms
  
  -- if two pairs have the same second symbol, their first symbols should also be the same
  guard $ pairs |> concat |> nubSort |> fmap snd |> anySame |> not

-- | Check whether a list of cofractions are compatible.
--   Cofraction @(n, d)@ and cofraction @(n', d')@ are compatible if @d . q = d' . q'@
--   implies @n . q = n' . q'@ for all `q` and 'q''.  That is, two cofractions are
--   compatible if their extensions are unique on the denominator.
--   A valid cofraction is compatible with itself.
--   For simplicity, we assume that the denominators of cofractions are edges of the node.
--   In fact, we only deal with fractions and cofractions whose denominators are
--   nondecomposable.
compatibleCofractions :: Monoid e => BAC e -> [Cofraction] -> Bool
compatibleCofractions _ [] = True
compatibleCofractions node cofractions = isJust do
  -- ensure that all denominators/numerators of cofractions end at the same node
  (_, sym0) <-
    cofractions
    |> fmap (both (arrow2 node .> fromJust .> uncurry join .> symbol))
    |> guarded allSame
    |> fmap head
  
  sequence_ $ node |> foldUnder sym0 \curr results -> do
    results' <- traverse sequence results

    -- find extended cofraction whose vertex is this node, and return two symbols referencing
    -- the denominator and the numerator of this cofraction.
    let pairs = do
          (res, edge) <- results' `zip` edges (target curr)
          case res of
            AtOuter -> mzero
            AtInner subpairs -> subpairs |> fmap (both (dict edge !))
            AtBoundary ->
              cofractions
              |> find (snd .> (== symbol2 (curr, edge)))
              |> fmap (both snd)
              |> maybe mzero return

    -- if two pairs have the same second symbol, their first symbols should also be the same
    pairs |> nubSort |> guarded (fmap snd .> anySame .> not)

-- | Check whether cofractions and fractions are compatible each others.
--   Cofraction @(n, d)@ and fraction @(n', d')@ are compatible if @n' . d = d' . n@.
compatibleCofractionsFractions :: Monoid e => BAC e -> [Cofraction] -> [Fraction] -> Bool
compatibleCofractionsFractions node cofractions fractions =
  isJust $
    cofractions |> traverse \(n_sym_sym, d_sym_sym) -> do
      fractions |> traverse \(n_sym_sym', d_sym_sym') -> do
        n_arr_arr <- arrow2 node n_sym_sym
        d_arr_arr <- arrow2 node d_sym_sym
        n_arr_arr' <- arrow2 node n_sym_sym'
        d_arr_arr' <- arrow2 node d_sym_sym'

        -- ensure ending node of the denominator of cofraction is the starting node of the
        -- numerator of fraction
        guard $ symbol (uncurry join d_arr_arr) == symbol (fst n_arr_arr')
        -- ensure ending node of the numerator of cofraction is the starting node of the
        -- denominator of fraction
        guard $ symbol (uncurry join n_arr_arr) == symbol (fst d_arr_arr')

        -- compose the denominator of cofraction and the numerator of fraction
        -- and compose the numerator of cofraction and the denominator of fraction
        -- they should be the same
        let arr = snd d_arr_arr `join` snd n_arr_arr'
        let arr' = snd n_arr_arr `join` snd d_arr_arr'
        guard $ symbol arr == symbol arr'

{- |
Find all valid nondecomposable cofractions and fractions, which is used for adding a
morphism.  The results are the fractions and cofractions need to be selected, or Nothing
if it is invalid.

Examples:

>>> fromJust $ findValidCofractionsFractions 1 6 cone
([[((0,1),(0,6))]],[])
-}
findValidCofractionsFractions ::
  Monoid e
  => Symbol
  -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol
  -- ^ The symbol indicating the target object of the morphism to be added.
  -> BAC e
  -- ^ The root node of BAC.
  -> Maybe ([[Cofraction]], [[Fraction]])
  -- ^ The cofractions and fractions need to be selected, or Nothing if it is invalid to
  --   add such morphism.
findValidCofractionsFractions src tgt node = do
  -- ensure that `src` and `tgt` are reachable, and check the order between `src` and `tgt`
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src == Outer

  let src_alts =
        suffixND node src
        |> nubSortOn symbol2
        |> fmap \(arr, edge) -> sort do
          -- construct nondecomposable cofraction and validate it
          arr' <- arr `divide` tgt_arr
          let cofraction = (symbol2 (arr, arr'), symbol2 (arr, edge))
          guard $ validateCofraction node cofraction
          return cofraction
  let tgt_alts =
        edgesND (target tgt_arr)
        |> nubSortOn symbol
        |> fmap \edge -> sort do
          -- construct nondecomposable fraction and validate it
          arr' <- src_arr `divide` (tgt_arr `join` edge)
          let fraction = (symbol2 (src_arr, arr'), symbol2 (tgt_arr, edge))
          guard $ validateFraction node fraction
          return fraction
  return (src_alts, tgt_alts)
  
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
([[((0,1),(0,6))]],[])
>>> printBAC $ fromJust $ addNDSymbol 1 6 2 [((0,1),(0,6))] [] cone
- 0->1; 1->2; 2->6
  - 0->1
    &0
  - 0->2
    &1
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &2
    - 0->1
      *0
    - 0->2
      *1
  - 0->4; 1->2; 2->3
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
  fromReachable src_node' $ node |> modifyUnder src \(curr, edge) -> \case
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

>>> printBAC $ fromJust $ addLeafNode 2 1 (makeShifter cone 1) cone
- 0->1; 1->2; 2->8
  - 0->1; 1->2
    &0
    - 0->1
- 0->3; 1->4; 2->2; 3->6; 4->4; 6->8
  - 0->1; 1->2; 2->3; 3->6
    &1
    - 0->1; 1->3
      *0
    - 0->2
  - 0->4; 1->2; 2->3; 3->6
    *1

>>> printBAC $ fromJust $ addLeafNode 4 3 (makeShifter cone 1) cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->10; 8->10
  - 0->1; 1->2; 2->3; 3->5
    &1
    - 0->1
      *0
    - 0->2
    - 0->3
  - 0->4; 1->2; 2->3; 3->8
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
    node |> modifyUnder src \(curr, edge) -> \case
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
>>> printBAC $ fromJust $ addParentNode (3,1) 5 mapping (makeShifter cone 1) cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->9
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
  - 0->5; 1->1; 2->2; 3->3
    - 0->1; 1->2; 2->3
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
    node |> modifyUnder src \(curr, edge) -> \case
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
