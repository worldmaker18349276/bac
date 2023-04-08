{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Algorithm (
  -- * Empty, Singleton

  empty,
  singleton,

  -- * Remove Morphism, Object

  missingAltPaths,
  removeMorphism,
  removeObject,
  removeInitialMorphism',
  removeObject',

  -- * Add Morphism

  Coangle,
  Angle,
  validateCoangle,
  validateAngle,
  compatibleAngles,
  compatibleCoangles,
  compatibleCoanglesAngles,
  findValidCoanglesAngles,
  addMorphism,

  -- * Split Morphism, Object, Category

  partitionPrefix,
  splitMorphism,
  partitionSymbols,
  splitObject,
  splitCategory,
  duplicateObject,
  duplicateObject',

  -- * Merge Morphisms, Objects, Categories

  mergeMorphisms,
  mergeObjects,
  mergeCategories,

  -- * Advanced Operations

  trimObject,
  appendObject,
  insertObject,
  expandMergingSymbols,
  mergeMorphismsAggressively,
) where

import Control.Arrow ((&&&))
import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (bimap, first, second))
import Data.Foldable (find)
import Data.Foldable.Extra (notNull)
import Data.List (elemIndex, elemIndices, findIndex, nub, sort, sortOn, transpose, uncons)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, nubSortOn, (!?))
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import Data.Tuple.Extra (both)
import Numeric.Natural (Natural)

import BAC.Base
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils (foldlMUncurry, guarded, (.>), (|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
An empty node.

Examples:

>>> printNode empty
-}
empty :: Node
empty = fromEdges []

{- |
An singleton node.

Examples:

>>> printNode singleton
- 0->1
-}
singleton :: Node
singleton = fromEdges [new_edge]
  where
  new_sym = base + 1
  new_dict = Map.singleton base new_sym
  new_node = empty
  new_edge = Arrow {dict = new_dict, target = new_node}

{- |
Find all missing alternative paths for a nondecomposable morphism, which are necessary for
removing this morphism.

Examples:

>>> missingAltPaths (3,1) cone
Just ([],[])

>>> missingAltPaths (4,2) cone
Just ([(3,3)],[])

>>> missingAltPaths (0,3) cone
Just ([],[(0,4)])
-}
missingAltPaths ::
  (Symbol, Symbol)  -- ^ The tuple of symbols indicating the morphism to be removed.
  -> Node           -- ^ The root node of BAC.
  -> Maybe ([(Symbol, Symbol)], [(Symbol, Symbol)])
                    -- ^ Tuples of symbols indicating the edges need to be added.
                    --   The first list is the edges skipping the source object, and the
                    --   second list is the edges skipping the target object.
missingAltPaths (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, tgt_arr) <- arrow2 node (src, tgt)
  guard $ nondecomposable (target src_arr) tgt
  let src_alts = nubSort do
        (arr1, arr2) <- src |> suffixND node
        guard $
          suffix (target arr1) (symbol (arr2 `join` tgt_arr))
          |> all (first (join arr1) .> symbol2 .> (== (src, tgt)))
        return $ symbol2 (arr1, arr2 `join` tgt_arr)
  let tgt_alts = nubSort do
        arr <- target tgt_arr |> edgesND
        guard $
          prefix (target src_arr) (symbol (tgt_arr `join` arr))
          |> all (fst .> (src_arr,) .> symbol2 .> (== (src, tgt)))
        return $ symbol2 (src_arr, tgt_arr `join` arr)
  return (src_alts, tgt_alts)

{- |
Remove a morphism.

Examples:

>>> printNode $ fromJust $ removeMorphism (1, 1) cone
- 0->1
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> removeMorphism (4, 2) cone
Nothing

>>> cone' = fromJust $ rewireEdges 0 [1, 4, 3] cone
>>> printNode $ fromJust $ removeMorphism (0, 3) cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2

>>> :{
printNode $
  cone
  |> removeMorphism (3, 1)
  |> fromJust
  |> rewireEdges 3 [4, 2, 3]
  |> fromJust
  |> rewireEdges 0 [1, 3, 4]
  |> fromJust
  |> removeMorphism (3, 4)
  |> fromJust
:}
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3
    &1
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
    *1
-}
removeMorphism ::
  (Symbol, Symbol)  -- ^ The tuple of symbols indicating the morphism to be removed.
  -> Node
  -> Maybe Node
removeMorphism (src, tgt) node = do
  guard $ missingAltPaths (src, tgt) node == Just ([],[])

  let src_node = arrow node src |> fromJust |> target
  let res0 = src_node |> edges |> filter (\edge -> symbol edge /= tgt) |> fromEdges
  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = filtered_dict, target = res0}
      where
      filtered_dict = dict edge |> Map.delete tgt

{- |
Remove a leaf node.

Examples:

>>> printNode $ fromJust $ removeObject 6 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 4->4
  - 0->1; 1->2
    &1
    - 0->1
      *0
  - 0->4; 1->2
    *1

>>> printNode $ fromJust $ removeObject 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0

>>> removeObject 4 cone
Nothing
-}
removeObject ::
  Symbol  -- ^ The symbol indicates the object to be removed.
  -> Node
  -> Maybe Node
removeObject tgt node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_node = arrow node tgt |> fromJust |> target
  guard $ tgt_node |> edges |> null

  fromReachable tgt_node $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtBoundary -> mzero
    AtInner res -> return edge {dict = filtered_dict, target = res}
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

{- |
Remove a morphism step by step: removing all related morphisms, then splitting category.

Examples:

>>> cone' = fromJust $ rewireEdges 0 [1, 4, 3] cone
>>> printNode $ fromJust $ removeInitialMorphism' 3 cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
-}
removeInitialMorphism' :: Symbol -> Node -> Maybe Node
removeInitialMorphism' tgt node = do
  guard $
    missingAltPaths (0, tgt) node
    |> maybe False \(l, r) -> null l && null r

  let remove_list =
        arrow node tgt
        |> fromJust
        |> target
        |> arrows
        |> fmap symbol
        |> filter (/= base)
        |> fmap (tgt,)
        |> reverse

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let ([], add_list') = node |> missingAltPaths sym2 |> fromJust
    node <- (node, add_list') |> foldlMUncurry \(node, (s1, s2)) -> do
      let new_edges =
            arrow node s1
            |> fromJust
            |> target
            |> edges
            |> fmap symbol
            |> (s2 :)
      return $ node |> rewireEdges s1 new_edges |> fromJust

    return $ node |> removeMorphism sym2 |> fromJust

  let keys = partitionSymbols node |> fmap \syms -> if tgt `elem` syms then 0 else 1
  return $ node |> splitCategory keys |> fromJust |> (! 1)


{- |
Remove an object step by step: removing all related morphisms, then splitting category.

Examples:

>>> printNode $ fromJust $ removeObject' 6 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 4->4
  - 0->1; 1->2
    &1
    - 0->1
      *0
  - 0->4; 1->2
    *1

>>> printNode $ fromJust $ removeObject' 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0

>>> removeObject' 4 cone
Nothing
-}
removeObject' :: Symbol -> Node -> Maybe Node
removeObject' tgt node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  guard $ tgt_arr |> target |> edges |> null

  let remove_list =
        node
        |> arrowsUnder tgt
        |> concatMap (\curr ->
          curr `divide` tgt_arr
          |> fmap (curr,)
          |> fmap symbol2
        )
        |> filter (fst .> (/= base))

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let (add_list, []) = node |> missingAltPaths sym2 |> fromJust
    node <- (node, add_list) |> foldlMUncurry \(node, (s1, s2)) -> do
      let new_edges =
            arrow node s1
            |> fromJust
            |> target
            |> edges
            |> fmap symbol
            |> (s2 :)
      return $ node |> rewireEdges s1 new_edges |> fromJust

    return $ node |> removeMorphism sym2 |> fromJust

  let keys = partitionSymbols node |> fmap \syms -> if tgt `elem` syms then 0 else 1
  return $ node |> splitCategory keys |> fromJust |> (! 1)

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
validateCoangle :: Node -> Coangle -> Bool
validateCoangle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (fst arr_arr1) == symbol (fst arr_arr2)
  guard $
    fst sym_sym1
    |> suffixND node
    |> groupSortOn (\(a1, a2) -> symbol2 (a1, a2 `join` snd arr_arr1))
    |> fmap (fmap \(a1, a2) -> symbol2 (a1, a2 `join` snd arr_arr2))
    |> all allSame

-- | Check whether a given value is a valid angle.
validateAngle :: Node -> Angle -> Bool
validateAngle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (uncurry join arr_arr1) == symbol (uncurry join arr_arr1)
  guard $
    target (snd arr_arr1)
    |> edgesND
    |> groupSortOn (\a -> symbol (snd arr_arr1 `join` a))
    |> fmap (fmap \a -> symbol (snd arr_arr2 `join` a))
    |> all allSame

-- | Check whether a list of angles are compatible.
--   Angle @(f, g)@ and angle @(f', g')@ are compatible if @h . f = h . f'@ implies
--   @h . g = h . g'@ for all `h`.
compatibleAngles :: Node -> [Angle] -> Bool
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
compatibleCoangles :: Node -> [Coangle] -> Bool
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
compatibleCoanglesAngles :: Node -> [Coangle] -> [Angle] -> Bool
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
  -> Node     -- ^ The root node of BAC.
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
Add a symbol in a node.

Examples:

>>> printNode $ fromJust $ addMorphism 1 6 2 [0] [] cone
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
addMorphism ::
  Symbol     -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol  -- ^ The symbol indicating the target object of the morphism to be added.
  -> Symbol  -- ^ The symbol to be added.
  -> [Int]   -- ^ The indices of coangles given by `findValidCoanglesAngles`.
  -> [Int]   -- ^ The indices of angles given by `findValidCoanglesAngles`.
  -> Node
  -> Maybe Node
addMorphism src tgt sym src_alts tgt_alts node = do
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
Partition the prefixes of a morphism.
It returns a partition of `prefix` of the given symbol, where the objects represented by
the elements in each group are unsplittable in the section category of the arrow specified
by `tgt`.

Examples:

>>> partitionPrefix cone 2
[[(1,1)],[(3,2)]]
-}
partitionPrefix :: Node -> Symbol -> [[(Symbol, Symbol)]]
partitionPrefix node tgt =
  prefix node tgt
  |> concatMap (\(arr1, arr23) -> suffix (target arr1) (symbol arr23) |> fmap (arr1,))
  |> fmap (\(arr1, (arr2, arr3)) -> ((arr1, arr2 `join` arr3), (arr1 `join` arr2, arr3)))
  |> fmap (both symbol2)
  |> bipartiteEqclass
  |> fmap fst
  |> fmap sort
  |> sort

{- |
Split a symbol on a node.

Examples:

>>> printNode $ fromJust $ splitMorphism (0,2) [0,1] cone
- 0->1; 1->2
  - 0->1
- 0->3; 1->4; 2->8; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> printNode $ fromJust $ splitMorphism (3,2) [0,1] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 6->2
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->6; 2->3
    *1
-}
splitMorphism ::
  (Symbol, Symbol)  -- ^ The symbols reference to the morphism to split.
  -> [Natural]      -- ^ The keys to classify splittable groups given by `partitionPrefix`.
  -> Node
  -> Maybe Node
splitMorphism (src, tgt) splittable_keys node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let splittable_groups = partitionPrefix (target src_arr) tgt
  guard $ length splittable_groups == length splittable_keys

  let src_syms = target src_arr |> symbols
  let splitted_syms =
        splittable_keys |> fmap (\i -> maximum src_syms * i + tgt)

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let sym0 = symbol edge
        if sym0 == tgt
        then do
          r' <- splitted_syms
          let split (s, r) = if r == tgt then (s, r') else (s, r)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          return edge {dict = splitted_dict}
        else do
          let split (s, r) = if r == tgt then (s, r') else (s, r)
                where
                r' =
                  splittable_groups
                  |> findIndex ((sym0, s) `elem`)
                  |> fromJust
                  |> (splitted_syms !!)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          return edge {dict = splitted_dict}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = merged_dict, target = res0}
      where
      merge (s, r)
        | s == tgt  = [(s', r) | s' <- splitted_syms]
        | otherwise = [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

{- |
Partition symbols of a object.
It returns a partition of `symbols` of the given node, where the objects represented by
the elements in each group are unsplittable in the given bounded acyclic category.

Examples:

>>> partitionSymbols $ cone
[[1,2,3,4,6]]

>>> partitionSymbols $ target $ fromJust $ arrow crescent 1
[[1,2,3],[5,6,7]]
-}
partitionSymbols :: Node -> [[Symbol]]
partitionSymbols =
  edges
  .> fmap (dict .> Map.elems)
  .> zip [0 :: Int ..]
  .> concatMap sequence
  .> bipartiteEqclass
  .> fmap (snd .> sort)
  .> sort

{- |
Split a node referenced by a symbol.

Examples:

>>> printNode $ fromJust $ splitObject 1 [0,1] crescent
- 0->1; 1->2; 2->3; 3->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
- 0->5; 5->2; 6->3; 7->4
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
-}
splitObject ::
  Symbol         -- ^ The symbol referencing the node to be splitted.
  -> [Natural]   -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> Node
  -> Maybe Node
splitObject tgt splittable_keys node = do
  guard $ locate (root node) tgt |> (== Inner)
  res0 <- arrow node tgt |> fromJust |> target |> splitCategory splittable_keys

  let splitSym :: [Symbol] -> Symbol -> [Symbol]
      splitSym syms s =
        splittable_keys |> fmap (\i -> maximum syms * i + s)

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      s_syms = target edge |> symbols
      r_syms = target curr |> symbols
      duplicate (s, r)
        | dict curr ! r == tgt = splitSym s_syms s `zip` splitSym r_syms r
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      let r_syms = target curr |> symbols
      let splitted_syms = splitSym r_syms (symbol edge)
      (sym, key) <- splitted_syms `zip` splittable_keys
      let res = res0 ! key
      let split (s, r)
            | s == base                    = Just (base, sym)
            | locate (root res) s == Inner = Just (s, r)
            | otherwise                    = Nothing
      let splitted_dict =
            dict edge |> Map.toList |> mapMaybe split |> Map.fromList
      return edge {dict = splitted_dict, target = res}

{- |
Split a root node.

Examples:

>>> let crescent_1 = target $ fromJust $ arrow crescent 1
>>> traverse_ printNode $ fromJust $ splitCategory [0,1] crescent_1
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2
  - 0->1
    *0
- 0->5; 1->6
  - 0->1
    &0
- 0->7; 1->6
  - 0->1
    *0
-}
splitCategory ::
  [Natural]  -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> Node
  -> Maybe (Map Natural Node)
splitCategory splittable_keys node = do
  let splittable_groups = partitionSymbols node
  guard $ length splittable_groups == length splittable_keys

  let splitted_keys = splittable_keys |> nub
  let splitted_groups =
        splitted_keys
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))

  return $ Map.fromList do
    (key, group) <- splitted_keys `zip` splitted_groups
    let splitted_edges =
          node |> edges |> filter (\edge -> symbol edge `elem` group)
    return (key, fromEdges splitted_edges)

{- |
Duplicate a node referenced by a symbol.

Examples:

>>> printNode $ fromJust $ duplicateObject 3 [0,1] crescent
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4; 9->7; 13->7
  - 0->1; 1->2; 2->9
    &0
    - 0->1
      &1
    - 0->2
      &2
  - 0->3; 1->2; 2->9
    &3
    - 0->1
      *1
    - 0->2
      *2
  - 0->5; 1->6; 2->13
    *0
  - 0->7; 1->6; 2->13
    *3
-}
duplicateObject :: Symbol -> [Natural] -> Node -> Maybe Node
duplicateObject tgt keys node = do
  guard $ locate (root node) tgt |> (== Inner)
  guard $ keys |> anySame |> not
  guard $ 0 `elem` keys
  let res0 = arrow node tgt |> fromJust |> target

  let splitSym :: [Symbol] -> Symbol -> [Symbol]
      splitSym syms s = keys |> fmap (\i -> maximum syms * i + s)

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      s_syms = target edge |> symbols
      r_syms = target curr |> symbols
      duplicate (s, r)
        | dict curr ! r == tgt = splitSym s_syms s `zip` splitSym r_syms r
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      let r_syms = target curr |> symbols
      let splitted_syms = splitSym r_syms (symbol edge)
      sym <- splitted_syms
      let split (s, r)
            | s == base                     = Just (base, sym)
            | locate (root res0) s == Inner = Just (s, r)
            | otherwise                     = Nothing
      let splitted_dict =
            dict edge |> Map.toList |> mapMaybe split |> Map.fromList
      return edge {dict = splitted_dict, target = res0}

{- |
Duplicate a node referenced by a symbol step by step.

Examples:

>>> printNode $ fromJust $ duplicateObject' 3 [0,1] crescent
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4; 9->7; 15->7
  - 0->1; 1->2; 2->9
    &0
    - 0->1
      &1
    - 0->2
      &2
  - 0->3; 1->2; 2->9
    &3
    - 0->1
      *1
    - 0->2
      *2
  - 0->5; 1->6; 2->15
    *0
  - 0->7; 1->6; 2->15
    *3
-}
duplicateObject' :: Symbol -> [Natural] -> Node -> Maybe Node
duplicateObject' tgt keys node = do
  guard $ locate (root node) tgt |> (== Inner)
  guard $ keys |> anySame |> not
  guard $ 0 `elem` keys

  let tgt_arr = arrow node tgt |> fromJust
  let split_list =
        node
        |> arrowsUnder tgt
        |> concatMap (\curr -> curr `divide` tgt_arr |> fmap (curr,))
        |> filter (\(arr1, arr2) -> not $ nondecomposable (target arr1) (symbol arr2))
        |> fmap symbol2

  let dup_list = suffixND node tgt |> fmap symbol2
  let origin_node = node

  let arrSS ss = arrow2 node ss |> fromJust |> snd
  let joinSS ss1 ss2 = (fst ss1, symbol (arrSS ss1 `join` arrSS ss2))
  let splitSym i (s1, s2) = (s1, maximum syms * i + s2)
        where
        syms = arrow origin_node s1 |> fromJust |> target |> symbols
  node <- (node, dup_list) |> foldlMUncurry \(node, dup_ss) -> do
    let angs = node |> findValidCoanglesAngles (fst dup_ss) tgt |> fromJust
    let src_alts =
          fst angs
          |> fmap ((findIndex \(ss1, ss2) -> ss1 `joinSS` dup_ss == ss2) .> fromJust)
    let tgt_alts =
          snd angs
          |> fmap ((findIndex \(ss1, ss2) -> dup_ss `joinSS` ss1 == ss2) .> fromJust)
    let new_syms = [snd (splitSym i dup_ss) | i <- keys, i /= 0]
    (node, new_syms) |> foldlMUncurry \(node, new_sym) ->
      return $
        node
        |> addMorphism (fst dup_ss) tgt new_sym src_alts tgt_alts
        |> fromJust

  (node, split_list) |> foldlMUncurry \(node, split_ss) -> do
    let (src_arr, tgt_subarr) = arrow2 node split_ss |> fromJust
    let origin_subnode = arrow2 origin_node split_ss |> fromJust |> fst |> target
    let splitSym' i (s1, s2) = (s1, maximum syms * i + s2)
          where
          syms = arrow origin_subnode s1 |> fromJust |> target |> symbols
    let origin_symbols =
          prefixND origin_subnode (snd split_ss) |> fmap symbol2
    let splitted_symbols =
          keys |> fmap (\i -> origin_symbols |> fmap (splitSym' i))
    let splittable_keys =
          partitionPrefix (target src_arr) (symbol tgt_subarr)
          |> fmap head
          |> fmap \ss ->
            splitted_symbols |> findIndex (elem ss) |> fromJust |> (keys !!)

    return $ node |> splitMorphism split_ss splittable_keys |> fromJust

{- |
Merge symbols on a node.

Examples:

>>> printNode $ fromJust $ mergeMorphisms (1,[2,3,6,8]) torus
- 0->1; 1->2; 2->3; 4->5; 7->2; 10->5
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->4; 1->2; 2->2
    &2
    - 0->1
      *1
    - 0->2
      *1
  - 0->7; 1->2; 2->2
    *0
  - 0->10; 1->2; 2->2
    *2
-}
mergeMorphisms ::
  (Symbol, [Symbol])  -- ^ The symbol referencing the node and symbols to be merged.
  -> Node
  -> Maybe Node
mergeMorphisms (src, tgts) node = do
  guard $ notNull tgts
  src_arr <- arrow node src
  tgt_arrs <- tgts |> traverse (arrow (target src_arr))
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  guard $
    src /= base
    || (tgt_arrs |> fmap (target .> edges .> fmap dict) |> allSame)
  guard $ suffix node src |> all \(_, edge) -> tgts |> fmap (dict edge !) |> allSame

  let merge s = if s `elem` tgts then head tgts else s

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let dict' = dict edge |> Map.toList |> fmap (second merge) |> Map.fromList
        return edge {dict = dict'}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict', target = res0}
      where
      dict' = dict edge |> Map.toList |> fmap (first merge) |> Map.fromList

newtype Tree a = Tree (Map a (Tree a)) deriving (Eq, Ord, Show)

forwardMaxChainTrieUnder :: Symbol -> Node -> Maybe (Tree (Symbol, Symbol))
forwardMaxChainTrieUnder sym = fromReachable res0 . foldUnder sym \curr results ->
  edges (target curr) `zip` results
  |> mapMaybe (second (fromReachable res0) .> sequence)
  |> fmap (first symbol)
  |> filter (fst .> nondecomposable (target curr))
  |> fmap (first (symbol curr,))
  |> nubSortOn fst
  |> Map.fromList
  |> Tree
  where
  res0 = Tree Map.empty

backwardMaxChainTrieUnder :: Symbol -> Node -> Maybe (Tree (Symbol, Symbol))
backwardMaxChainTrieUnder sym =
  forwardMaxChainTrieUnder sym .> fmap (fromTrie .> fmap reverse .> toTrie)
  where
  fromTrie :: Ord a => Tree a -> [[a]]
  fromTrie (Tree trie) =
    trie
    |> Map.toList
    |> fmap (fmap fromTrie)
    |> concatMap sequence
    |> fmap (uncurry (:))
  toTrie :: Ord a => [[a]] -> Tree a
  toTrie =
    fmap (uncons .> fromJust)
    .> groupSortOn fst
    .> fmap ((head .> fst) &&& (fmap snd .> toTrie))
    .> Map.fromList
    .> Tree

{- |
Check lower isomorphisms for given symbols.

Examples:

>>> lowerIso [2,4] [[0,1::Int], [0,1]] crescent
True
-}
lowerIso ::
  Eq k
  => [Symbol]  -- ^ The symbols to check.
  -> [[k]]     -- ^ The keys to classify nondecomposable incoming morphisms.
  -> Node
  -> Bool
lowerIso [] _ _ = True
lowerIso [_] _ _ = True
lowerIso tgts keys node = isJust do
  let tgt_pars = tgts |> fmap (suffixND node)
  guard $ tgt_pars |> fmap length |> allSame
  guard $ length keys == length tgt_pars
  guard $ keys `zip` tgt_pars |> fmap (length `bimap` length) |> all (uncurry (==))

  guard $ keys |> all (anySame .> not)
  indices <- keys |> traverse (traverse (`elemIndex` head keys))
  let merging_symbols =
        zip tgt_pars indices
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose
        |> fmap (fmap symbol2)
  guard $ merging_symbols |> all (fmap fst .> allSame)

  sequence_ $ node |> foldUnder (head tgts) \curr results -> do
    results' <- results |> traverse sequence

    let collapse = nubSort $ fmap sort do
          (lres, edge) <- results' `zip` edges (target curr)
          case lres of
            AtOuter -> mzero
            AtInner res -> res |> fmap (fmap (dict edge !))
            AtBoundary ->
              merging_symbols
              |> filter (head .> fst .> (== symbol curr))
              |> fmap (fmap snd)

    guard $ collapse |> concat |> anySame |> not

    return collapse

{- |
Merge nodes.

Examples:

>>> printNode $ fromJust $ mergeObjects [2,4] [[0,1], [0,1]] crescent
- 0->1; 1->2; 2->3; 5->2; 6->3
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->5; 1->6; 2->6
    *0
-}
mergeObjects ::
  [Symbol]        -- ^ The symbols referencing the nodes to be merged.
  -> [[Natural]]  -- ^ The merging table of nondecomposable incoming morphisms of the nodes.
                  --   The arrows with the same key will be merged.
  -> Node
  -> Maybe Node
mergeObjects tgts keys node = do
  guard $ notNull tgts
  guard $ lowerIso tgts keys node

  let tgt = head tgts
  let tgt_nodes = tgts |> fmap (arrow node .> fromJust .> target)
  let tgt_pars = tgts |> fmap (suffixND node)
  let merging_arrs =
        keys
        |> fmap (fmap ((`elemIndex` head keys) .> fromJust))
        |> zip tgt_pars
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose

  let merged_node = mergeCategories tgt_nodes
  let merging_offsets = tgt_nodes |> fmap (symbols .> maximum) |> scanl (+) 0

  let nd_merged_dicts = Map.fromList do
        arr_arrs <- merging_arrs
        let merged_wire =
              arr_arrs |> head |> snd |> symbol |> (base,)
        let merged_dict =
              arr_arrs
              |> fmap (snd .> dict .> Map.delete base .> Map.toList)
              |> zip merging_offsets
              |> concatMap (\(offset, dict) -> dict |> fmap (first (+ offset)))
              |> (merged_wire :)
              |> Map.fromList
        key <- arr_arrs |> fmap symbol2
        return (key, merged_dict)

  let find_merged_dict (arr1, arr23) =
        suffixND (target arr1) (symbol arr23)
        |> head
        |> \(arr2, arr3) ->
          (arr1 `join` arr2, arr3)
          |> symbol2
          |> (`Map.lookup` nd_merged_dicts)
          |> fromJust
          |> cat (dict arr2)

  fromReachable node $
    node |> foldUnder tgt \curr results ->
      let collapsed_edges = do
            (res, edge) <- results `zip` edges (target curr)
            let is_tgt = symbol (curr `join` edge) `elem` tgts
            let collapsed_node =
                  if is_tgt
                  then merged_node
                  else res |> fromInner |> fromMaybe (target edge)
            let collapsed_dict =
                  if is_tgt
                  then find_merged_dict (curr, edge)
                  else dict edge |> Map.filter (\sym -> dict curr ! sym `notElem` tail tgts)
            return edge {dict = collapsed_dict, target = collapsed_node}

      in fromEdges collapsed_edges

{- |
Merge multiple nodes.

Examples:

>>> printNode (mergeCategories [singleton, singleton, empty, singleton])
- 0->1
- 0->2
- 0->3

>>> printNode (mergeCategories [singleton, crescent])
- 0->1
- 0->2; 1->3; 2->4; 3->5; 5->3; 6->4; 7->5
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
-}
mergeCategories :: [Node] -> Node
mergeCategories nodes = fromEdges merged_edges
  where
  offsets = nodes |> fmap (symbols .> maximum) |> scanl (+) 0
  merged_edges = do
    (offset, node) <- zip offsets nodes
    edge <- edges node
    let dict' = dict edge |> fmap (+ offset)
    return edge {dict = dict'}

trimObject :: Symbol -> Node -> Maybe Node
trimObject tgt node = do
  guard $ locate (root node) tgt |> (== Inner)
  tgt_arr <- arrow node tgt

  fromReachable (target tgt_arr) $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtBoundary -> do
      subedge <- target edge |> edges
      let concated_dict = dict edge `cat` dict subedge
      return subedge {dict = concated_dict}
    AtInner res -> return edge {dict = filtered_dict, target = res}
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

appendObject :: Symbol -> Node -> Maybe Node
appendObject src node = do
  src_arr <- arrow node src
  let res0 = mergeCategories [target src_arr, singleton]
  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) lres -> case fromReachable res0 lres of
      Nothing -> return edge
      Just res -> return edge {dict = new_dict, target = res}
        where
        new_sym = symbols (target curr) |> maximum |> (+ 1)
        new_sym' = symbols (target edge) |> maximum |> (+ 1)
        new_dict = dict edge |> Map.insert new_sym' new_sym

insertObject :: (Symbol, Maybe Symbol) -> Node -> Maybe Node
insertObject (src, tgt) node = do
  src_arr <- arrow node src
  let new_sym = target src_arr |> symbols |> maximum |> (+ 1)
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- arrow (target src_arr) tgt
      let new_outdict = target tgt_arr |> symbols |> fmap (\s -> (s, s+1)) |> Map.fromList
      let new_outedge = Arrow {dict = new_outdict, target = target tgt_arr}
      let new_node = fromEdges [new_outedge]
      let new_indict = dict tgt_arr |> Map.mapKeys (+ 1) |> Map.insert base new_sym
      return Arrow {dict = new_indict, target = new_node}
    Nothing ->
      return Arrow {dict = Map.singleton base new_sym, target = empty}

  let res0 = fromEdges $ edges (target src_arr) ++ [new_inedge]

  fromReachable res0 $ node |> modifyUnder src \(curr, edge) res ->
    case fromReachable res0 res of
      Nothing -> return edge
      Just res -> return edge {dict = dict', target = res}
        where
        newSym syms = (+) (maximum syms + 1)
        s_syms = target curr |> symbols
        r_syms = target edge |> symbols
        dict' =
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if dict curr ! r == src
            then [(s, r), (newSym s_syms s, newSym r_syms r)]
            else [(s, r)]
          )
          |> Map.fromList

expandMergingSymbols :: Node -> [[Symbol]] -> [[Symbol]]
expandMergingSymbols node =
  fmap (fmap (arrow node .> fromJust .> dict .> Map.toList))
  .> zip [0 :: Integer ..]
  .> concatMap sequence
  .> concatMap sequence
  .> fmap (\(a, (b, c)) -> ((a, b), c))
  .> bipartiteEqclass
  .> fmap snd
  .> filter (length .> (> 1))
  .> fmap sort
  .> sort

mergeMorphismsAggressively :: Symbol -> [[Symbol]] -> Node -> Maybe Node
mergeMorphismsAggressively src tgts node = do
  src_arr <- arrow node src

  tgt_arrs <- tgts |> traverse (traverse (arrow (target src_arr)))
  guard $ tgt_arrs |> all (fmap target .> allSame)

  let mergeSymbol tgts' s = tgts' |> find (elem s) |> fmap head |> fromMaybe s

  let merging_lists = expandMergingSymbols (target src_arr) tgts
  let merged_node = fromEdges do
        arr <- target src_arr |> edges
        let merged_dict = dict arr |> fmap (mergeSymbol merging_lists)
        return arr {dict = merged_dict}
  let res0 = (merged_node, merging_lists)

  lres <- sequence $
    node |> foldUnder src \curr results -> do
      results' <- traverse sequence results
      let merging_lists_of = fromReachable res0 .> fmap snd .> fromMaybe []
      let merging_lists =
            results'
            |> concatMap merging_lists_of
            |> zip (target curr |> edges |> fmap dict)
            |> fmap (sequence .> fmap (uncurry (!)))
            |> expandMergingSymbols (target curr)
      let merged_node = fromEdges do
            (lres, edge) <- results' `zip` edges (target curr)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol merging_lists)
                  |> Map.mapKeys (mergeSymbol (merging_lists_of lres))
            case fromReachable res0 lres of
              Nothing -> return edge {dict = merged_dict}
              Just (res, _) -> return edge {dict = merged_dict, target = res}
      return (merged_node, merging_lists)

  fromReachable merged_node $ fmap fst lres

