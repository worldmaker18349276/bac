{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Add (
  Coangle,
  Angle,
  validateCoangle,
  validateAngle,
  compatibleAngles,
  compatibleCoangles,
  compatibleCoanglesAngles,
  findValidCoanglesAngles,
  addNDSymbol,
  addLeafNode,
  addParentNode,
  addParentNodeOnRoot,
) where

import Control.Monad (mzero, guard)
import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.List (sort)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, snoc, (!?))
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import Control.Arrow ((&&&))
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

-- | Two tuples of symbols representing two morphisms where coforks of the first morphism
--   are also coforks of the second morphism.  A cofork of a morphism `f` is a pair of
--   distinct morphisms `g`, 'g'' such that @f . g = f . g'@.  This constraint shows the
--   possibility to add an edge between them.
type Coangle = ((Symbol, Symbol), (Symbol, Symbol))

-- | Two tuples of symbols representing two morphisms where forks of the first morphism are
--   also forks of the second morphism.  A fork of a morphism `f` is a pair of distinct
--   morphisms `g`, 'g'' such that @g . f = g' . f@.  This constraint shows the
--   possibility to add an edge between them.
type Angle = ((Symbol, Symbol), (Symbol, Symbol))

-- | Check whether a given value is a valid coangle.
validateCoangle :: BAC -> Coangle -> Bool
validateCoangle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (fst arr_arr1) == symbol (fst arr_arr2)
  guard $
    fst sym_sym1
    |> suffixND node
    |> groupSortOn (second (`join` snd arr_arr1) .> symbol2)
    |> fmap (fmap (second (`join` snd arr_arr2) .> symbol2))
    |> all allSame

-- | Check whether a given value is a valid angle.
validateAngle :: BAC -> Angle -> Bool
validateAngle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (uncurry join arr_arr1) == symbol (uncurry join arr_arr1)
  guard $
    target (snd arr_arr1)
    |> edgesND
    |> groupSortOn (join (snd arr_arr1) .> symbol)
    |> fmap (fmap (join (snd arr_arr2) .> symbol))
    |> all allSame

-- | Check whether a list of angles are compatible.
--   Angle @(f, g)@ and angle @(f', g')@ are compatible if @h . f = h . f'@ implies
--   @h . g = h . g'@ for all `h`.
compatibleAngles :: BAC -> [Angle] -> Bool
compatibleAngles node =
  traverse (\(sym_sym1, sym_sym2) -> do
    arr_arr1 <- arrow2 node sym_sym1
    arr_arr2 <- arrow2 node sym_sym2
    return $ Map.elems (dict (snd arr_arr1)) `zip` Map.elems (dict (snd arr_arr2))
  )
  .> maybe False (concat .> nubSort .> fmap fst .> anySame .> not)

-- | Check whether a list of coangles are compatible.
--   Coangle @(f, g)@ and coangle @(f', g')@ are compatible if @f . h = f' . h@ implies
--   @g . h = g' . h@ for all `h`.
compatibleCoangles :: BAC -> [Coangle] -> Bool
compatibleCoangles _ [] = True
compatibleCoangles node coangs =
  isJust $ sequence_ $ node |> foldUnder sym0 \curr results -> do
    results' <- traverse sequence results
    let pairs = do
          (res, edge) <- results' `zip` edges (target curr)
          case res of
            AtOuter -> mzero
            AtInner res -> res |> fmap (both (dict edge !))
            AtBoundary ->
              coangs
              |> find (fst .> (== symbol2 (curr, edge)))
              |> fmap (both snd)
              |> maybe mzero return
    pairs |> nubSort |> guarded (fmap fst .> anySame .> not)
  where
  sym0 = coangs |> head |> fst |> fst

-- | Check whether coangles and angles are compatible each others.
--   Coangle @(f, g)@ and angle @(g', f')@ are compatible if @f' . f = g' . g@.
compatibleCoanglesAngles :: BAC -> [Coangle] -> [Angle] -> Bool
compatibleCoanglesAngles node coangs angs =
  isJust $
    angs |> traverse \(sym_sym1, sym_sym2) -> do
      arr_arr1 <- arrow2 node sym_sym1
      arr_arr2 <- arrow2 node sym_sym2
      coangs |> traverse \(sym_sym1', sym_sym2') -> do
        arr_arr1' <- arrow2 node sym_sym1'
        arr_arr2' <- arrow2 node sym_sym2'
        guard $ symbol (uncurry join arr_arr1) == symbol (fst arr_arr2')
        guard $ symbol (uncurry join arr_arr2) == symbol (fst arr_arr1')
        guard $
          symbol (snd arr_arr1 `join` snd arr_arr2')
          == symbol (snd arr_arr2 `join` snd arr_arr1')

{- |
Find all valid coangles and angles, which is used for adding a morphism.  The results are
the angles and coangles need to be selected, or Nothing if it is invalid.

Examples:

>>> fromJust $ findValidCoanglesAngles 1 6 cone
([[((0,1),(0,6))]],[])
-}
findValidCoanglesAngles ::
  Symbol      -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol   -- ^ The symbol indicating the target object of the morphism to be added.
  -> BAC      -- ^ The root node of BAC.
  -> Maybe ([[Coangle]], [[Angle]])
              -- ^ The coangles and angles need to be selected, or Nothing if it is invalid.
findValidCoanglesAngles src tgt node = do
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src == Outer
  let src_alts = sort do
        (arr1, arr2) <- src |> suffixND node
        return $ sort do
          arr2' <- arr1 `divide` tgt_arr
          let ang = (symbol2 (arr1, arr2), symbol2 (arr1, arr2'))
          guard $ validateCoangle node ang
          return ang
  let tgt_alts = sort do
        edge <- target tgt_arr |> edgesND
        return $ sort do
          arr' <- src_arr `divide` (tgt_arr `join` edge)
          let ang = (symbol2 (tgt_arr, edge), symbol2 (src_arr, arr'))
          guard $ validateAngle node ang
          return ang
  return (src_alts, tgt_alts)

{- |
Add a nondecomposable symbol in a node (add a non-terminal nondecomposable morphism).

Examples:

>>> printBAC $ fromJust $ addNDSymbol 1 6 2 [0] [] cone
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
  Symbol     -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol  -- ^ The symbol indicating the target object of the morphism to be added.
  -> Symbol  -- ^ The symbol to be added.
  -> [Int]   -- ^ The indices of coangles given by `findValidCoanglesAngles`.
  -> [Int]   -- ^ The indices of angles given by `findValidCoanglesAngles`.
  -> BAC
  -> Maybe BAC
addNDSymbol src tgt sym src_alts tgt_alts node = do
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src |> (== Outer)

  let (src_angs, tgt_angs) = findValidCoanglesAngles src tgt node |> fromJust
  guard $ length src_angs == length src_alts
  guard $ length tgt_angs == length tgt_alts
  src_angs' <- src_angs `zip` src_alts |> traverse (uncurry (!?))
  tgt_angs' <- tgt_angs `zip` tgt_alts |> traverse (uncurry (!?))

  guard $ compatibleAngles node tgt_angs'
  guard $ compatibleCoanglesAngles node src_angs' tgt_angs'
  guard $ compatibleCoangles node src_angs'
  guard $ target src_arr |> symbols |> notElem sym

  let new_dict =
        tgt_angs'
        |> fmap (both (arrow2 node .> fromJust))
        |> concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
        |> ((base, sym) :)
        |> nubSort
        |> Map.fromList
  let new_edge = Arrow {dict = new_dict, target = target tgt_arr}

  let find_new_wire (arr1, arr23) =
        suffixND (target arr1) (symbol arr23)
        |> head
        |> \(arr2, arr3) ->
          src_angs'
          |> find (fst .> (== symbol2 (arr1 `join` arr2, arr3)))
          |> fromJust
          |> \(_, (_, s)) -> (dict arr2 ! sym, dict arr2 ! s)

  let res0 = target src_arr |> edges |> (++ [new_edge]) |> fromEdges
  fromReachable res0 $ node |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = new_dict, target = res0}
      where
      new_wire = find_new_wire (curr, edge)
      new_dict = dict edge |> uncurry Map.insert new_wire

{- |
Add a leaf node to a node (add a terminal nondecomposable morphism).

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
  Symbol             -- ^ The symbol referenced to the node to append.
  -> Symbol          -- ^ The symbol referenced to the added node.
  -> ((Symbol, Symbol) -> Symbol)
                     -- ^ The function to insert symbol to all ancestor nodes.
  -> BAC
  -> Maybe BAC
addLeafNode src sym inserter node = do
  src_arr <- arrow node src
  let src_node = target src_arr
  guard $ sym `notElem` symbols src_node
  guard $
    arrowsUnder node src |> all \curr ->
      curr `divide` src_arr
      |> fmap symbol
      |> fmap (symbol curr,)
      |> fmap inserter
      |> (++ symbols (target curr))
      |> anySame
      |> not

  let new_node = fromJust $ singleton sym
  let res0 = fromEdges (edges src_node ++ edges new_node)
  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) -> \case
      AtOuter -> return edge
      AtBoundary -> return edge {dict = new_dict, target = res0}
        where
        new_sym = inserter (symbol curr, symbol edge)
        new_dict = dict edge |> Map.insert sym new_sym
      AtInner res -> return edge {dict = new_dict, target = res}
        where
        new_wires =
          (curr `join` edge) `divide` src_arr
          |> fmap (\subarr -> ((curr `join` edge, subarr), (curr, edge `join` subarr)))
          |> fmap (both (symbol2 .> inserter))
        new_dict = new_wires |> foldr (uncurry Map.insert) (dict edge)

{- |
Insert a node in the middle of an arrow (add an object).

Examples:

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
  (Symbol, Symbol)       -- ^ The symbols indicate the arrow to be interpolated.
  -> Symbol              -- ^ The symbol referenced the added node.
  -> Dict                -- ^ The dictionary of the edge of the added node.
  -> ((Symbol, Symbol) -> Symbol)
                         -- ^ The function to insert symbol to all ancestor nodes.
  -> BAC
  -> Maybe BAC
addParentNode (src, tgt) sym mapping inserter node = do
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let tgt_arr = src_arr `join` tgt_subarr
  guard $ tgt /= base

  guard $ symbols (target tgt_subarr) |> (== Map.keys mapping)
  guard $ Map.elems mapping |> (base :) |> anySame |> not
  guard $ sym `notElem` symbols (target src_arr)
  guard $
    arrowsUnder node src |> all \curr ->
      curr `divide` tgt_arr
      |> fmap (symbol .> (symbol curr,) .> inserter)
      |> (++ symbols (target curr))
      |> anySame
      |> not

  let new_outedge = Arrow {dict = mapping, target = target tgt_subarr}
  let new_node = fromEdges [new_outedge]
  let new_indict = dict tgt_subarr |> Map.mapKeys (mapping !) |> Map.insert base sym
  let new_inedge = Arrow {dict = new_indict, target = new_node}
  let res0 = fromEdges $ edges (target src_arr) `snoc` new_inedge

  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) -> \case
      AtOuter -> return edge
      AtBoundary -> return edge {dict = new_dict, target = res0}
        where
        new_sym = inserter (symbol curr, symbol edge)
        new_dict = dict edge |> Map.insert sym new_sym
      AtInner res -> return edge {dict = new_dict, target = res}
        where
        new_wires =
          (curr `join` edge) `divide` src_arr
          |> fmap (\subarr -> ((curr `join` edge, subarr), (curr, edge `join` subarr)))
          |> fmap (both (symbol2 .> inserter))
        new_dict = new_wires |> foldr (uncurry Map.insert) (dict edge)

addParentNodeOnRoot :: Symbol -> Symbol -> Dict -> BAC -> Maybe BAC
addParentNodeOnRoot tgt sym mapping = addParentNode (base, tgt) sym mapping undefined
