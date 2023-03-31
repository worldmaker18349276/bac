{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module BAC.Algorithm where

import Control.Monad (guard, MonadPlus (mzero), void)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (find)
import Data.Foldable.Extra (notNull)
import Data.List (elemIndices, findIndex, sort, transpose, sortOn, nub)
import Data.List.Extra (nubSort, groupSortOn, allSame, nubSortOn, anySame, (!?))
import Data.Tuple.Extra (both)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe, fromJust, fromMaybe, isJust)

import Utils.Utils ((|>), (.>), guarded, label)
import Utils.DisjointSet (bipartiteEqclass, bipartiteEqclassOn)
import BAC.Base

-- $setup
-- The example code below runs with the following settings:
--
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)

-- * Empty, Singleton

{- |
An empty node.

Examples:

>>> printNode' empty
-}
empty :: Node e
empty = Node {edges = []}

{- |
An singleton node.

Examples:

>>> printNode' (singleton ())
- 0->1
-}
singleton ::
  e           -- ^ The data of the only edge.
  -> Node e   -- ^ The result.
singleton val = Node {edges = [(val, new_arr)]}
  where
  new_sym = base + 1
  new_dict = Map.singleton base new_sym
  new_node = empty
  new_arr = Arrow {dict = new_dict, target = new_node}

-- * Remove Morphism, Object

{- |
Prepare for removing a morphism.

Examples:

>>> fmap (both (fmap symbol2)) $ prepareForRemoveMorphism (3,1) cone
Just ([],[])

>>> fmap (both (fmap symbol2)) $ prepareForRemoveMorphism (4,2) cone
Just ([(3,3)],[])

>>> fmap (both (fmap symbol2)) $ prepareForRemoveMorphism (0,3) cone
Just ([],[(0,4)])
-}
prepareForRemoveMorphism ::
  (Symbol, Symbol)  -- ^ The tuple of symbols indicating the morphism to be removed.
  -> Node e         -- ^ The root node of BAC.
  -> Maybe ([(Arrow e, Arrow e)], [(Arrow e, Arrow e)])
                    -- ^ Tuples of arrows indicating the edges need to be added.
                    --   The first list is the edges skipping the source object, and the
                    --   second list is the edges skipping the target object.
prepareForRemoveMorphism (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, tgt_arr) <- arrow2 (src, tgt) node
  guard $ nondecomposable (target src_arr) tgt
  let src_alts = nubSortOn symbol2 do
        (arr1, arr2) <- src |> suffixND node
        guard $
          suffix (target arr1) (symbol (arr2 `join` tgt_arr))
          |> all (first (join arr1) .> symbol2 .> (== (src, tgt)))
        return (arr1, arr2 `join` tgt_arr)
  let tgt_alts = nubSortOn symbol2 do
        arr <- target tgt_arr |> arrowsND
        guard $
          prefix (target src_arr) (symbol (tgt_arr `join` arr))
          |> all (fst .> (src_arr,) .> symbol2 .> (== (src, tgt)))
        return (src_arr, tgt_arr `join` arr)
  return (src_alts, tgt_alts)

{- |
Remove a morphism.

Examples:

>>> printNode' $ fromJust $ removeMorphism (1, 1) cone
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
-}
removeMorphism ::
  (Symbol, Symbol)   -- ^ The tuple of symbols indicate the morphism to be removed.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
removeMorphism (src, tgt) node = do
  guard $
    prepareForRemoveMorphism (src, tgt) node
    |> maybe False \(l, r) -> null l && null r

  let src_node = node |> arrow src |> fromJust |> target
  let res0 = src_node |> edges |> filter (\(_, arr) -> symbol arr /= tgt) |> Node
  fromReachable res0 $ node |> modifyUnder src \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {dict = filtered_dict, target = res0})
      where
      filtered_dict = dict arr |> Map.delete tgt

{- |
Remove a leaf node.

Examples:

>>> printNode' $ fromJust $ removeObject 6 cone
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

>>> removeObject 4 cone
Nothing
-}
removeObject ::
  Symbol             -- ^ The symbol indicates the object to be removed.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
removeObject tgt node = do
  guard $ root node |> locate tgt |> (== Inner)
  tgt_arr <- node |> arrow tgt
  guard $ target tgt_arr |> edges |> null

  fromReachable (target tgt_arr) $ node |> modifyUnder tgt \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtBoundary -> mzero
    AtInner res -> return (value, arr {dict = filtered_dict, target = res})
      where
      filtered_dict = dict arr |> Map.filter (\s -> dict curr ! s /= tgt)

-- * Add Morphism

-- | Two tuples of arrows representing two morphisms where coforks of the first morphism
--   are also coforks of the second morphism.  A cofork of a morphism `f` is a pair of
--   distinct morphisms `g`, 'g'' such that @f . g = f . g'@.  This constraint shows the
--   possibility to add an edge between them.
type Coangle e = ((Arrow e, Arrow e), (Arrow e, Arrow e))

-- | Two tuples of arrows representing two morphisms where forks of the first morphism are
--   also forks of the second morphism.  A fork of a morphism `f` is a pair of distinct
--   morphisms `g`, 'g'' such that @g . f = g' . f@.  This constraint shows the
--   possibility to add an edge between them.
type Angle e = ((Arrow e, Arrow e), (Arrow e, Arrow e))

-- | Check whether a given value is a valid coangle.
validateCoangle :: Node e -> Coangle e -> Bool
validateCoangle node ((arr1, arr2), (arr1', arr2')) =
  symbol arr1 == symbol arr1'
  && (
    symbol arr1
    |> suffixND node
    |> groupSortOn (\(a1, a2) -> symbol2 (a1, a2 `join` arr2))
    |> fmap (fmap \(a1, a2) -> symbol2 (a1, a2 `join` arr2'))
    |> all allSame
  )

-- | Check whether a given value is a valid angle.
validateAngle :: Angle e -> Bool
validateAngle ((arr1, arr2), (arr1', arr2')) =
  symbol (arr1 `join` arr2) == symbol (arr1' `join` arr2')
  && (
    target arr2
    |> arrowsND
    |> groupSortOn (\a -> symbol (arr2 `join` a))
    |> fmap (fmap \a -> symbol (arr2' `join` a))
    |> all allSame
  )

-- | Check whether a list of angles are compatible.
--   Angle @(f, g)@ and angle @(f', g')@ are compatible if @h . f = h . f'@ implies
--   @h . g = h . g'@ for all `h`.
compatibleAngles :: [Angle e] -> Bool
compatibleAngles =
  concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
  .> nubSort
  .> fmap fst
  .> anySame
  .> not

-- | Check whether a list of coangles are compatible.
--   Coangle @(f, g)@ and coangle @(f', g')@ are compatible if @f . h = f' . h@ implies
--   @g . h = g' . h@ for all `h`.
compatibleCoangles :: Node e -> [Coangle e] -> Bool
compatibleCoangles _ [] = True
compatibleCoangles node angs =
  isJust $ sequence_ $ node |> foldUnder sym0 \curr results -> do
    results' <- traverse sequence results
    let pairs = do
          (res, arr) <- results' `zip` arrows (target curr)
          case res of
            AtOuter -> mzero
            AtInner res -> res |> fmap (both (dict arr !))
            AtBoundary ->
              angs
              |> find (fst .> symbol2 .> (== symbol2 (curr, arr)))
              |> fmap (both (snd .> symbol))
              |> maybe mzero return
    pairs |> nubSort |> guarded (fmap fst .> anySame .> not)
  where
  sym0 = angs |> head |> fst |> fst |> symbol

-- | Check whether coangles and angles are compatible each others.
--   Coangle @(f, g)@ and angle @(g', f')@ are compatible if @f' . f = g' . g@.
compatibleCoanglesAngles :: [Coangle e] -> [Angle e] -> Bool
compatibleCoanglesAngles src_angs tgt_angs =
  tgt_angs |> all \(_, (arr1, arr2)) ->
    let
      sym1 = dict arr1 ! base
      sym2 = dict arr2 ! base
    in
      src_angs |> all \(_, (arr2', arr1')) ->
        dict arr1' ! sym1 == dict arr2' ! sym2

{- |
Prepare for adding a morphism.  The results are the angles and coangles need to be
selected, or Nothing if it is invalid.

Examples:

>>> both (fmap (fmap (both symbol2))) $ fromJust $ prepareForAddMorphism 1 6 cone
([[((0,1),(0,6))]],[])
-}
prepareForAddMorphism ::
  Symbol      -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol   -- ^ The symbol indicating the target object of the morphism to be added.
  -> Node e   -- ^ The root node of BAC.
  -> Maybe ([[Coangle e]], [[Angle e]])
              -- ^ The coangles and angles need to be selected, or Nothing if it is invalid.
prepareForAddMorphism src tgt node = do
  src_arr <- arrow src node
  tgt_arr <- arrow tgt node
  guard $ locate src tgt_arr == Outer
  let src_alts = sortOn (fmap (both symbol2)) do
        (arr1, arr2) <- src |> suffixND node
        return $ sortOn (both symbol2) do
          arr2' <- arr1 `divide` tgt_arr
          let ang = ((arr1, arr2), (arr1, arr2'))
          guard $ validateCoangle node ang
          return ang
  let tgt_alts = sortOn (fmap (both symbol2)) do
        arr <- target tgt_arr |> arrowsND
        return $ sortOn (both symbol2) do
          arr' <- src_arr `divide` (tgt_arr `join` arr)
          let ang = ((tgt_arr, arr), (src_arr, arr'))
          guard $ validateAngle ang
          return ang
  return (src_alts, tgt_alts)

{- |
Add a symbol in a node.

Examples:

>>> printNode' $ fromJust $ addMorphism 1 6 [0] [] () cone
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
  Symbol             -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol          -- ^ The symbol indicating the target object of the morphism to be added.
  -> [Int]           -- ^ The indices of coangles given by `prepareForAddMorphism`.
  -> [Int]           -- ^ The indices of angles given by `prepareForAddMorphism`.
  -> e               -- ^ The value of the edge to be added.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
addMorphism src tgt src_alts tgt_alts val node = do
  src_arr <- node |> arrow src
  tgt_arr <- node |> arrow tgt
  guard $ tgt_arr |> locate src |> (== Outer)

  (src_angs, tgt_angs) <- prepareForAddMorphism src tgt node
  guard $ length src_angs == length src_alts
  guard $ length tgt_angs == length tgt_alts
  src_angs' <- src_angs `zip` src_alts |> traverse (uncurry (!?))
  tgt_angs' <- tgt_angs `zip` tgt_alts |> traverse (uncurry (!?))

  guard $ compatibleAngles tgt_angs'
  guard $ compatibleCoanglesAngles src_angs' tgt_angs'
  guard $ compatibleCoangles node src_angs'

  let new_sym = target src_arr |> symbols |> maximum |> (+ 1)
  let new_dict =
        tgt_angs'
        |> concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
        |> ((base, new_sym) :)
        |> nubSort
        |> Map.fromList
  let new_edge = (val, Arrow {dict = new_dict, target = target tgt_arr})

  let find_new_wire (arr1, arr23) =
        suffixND (target arr1) (symbol arr23)
        |> head
        |> \(arr2, arr3) ->
          src_angs'
          |> find (fst .> symbol2 .> (== symbol2 (arr1 `join` arr2, arr3)))
          |> fromJust
          |> \(_, (_, arr)) -> (dict arr2 ! new_sym, dict arr2 ! symbol arr)

  let res0 = target src_arr |> edges |> (++ [new_edge]) |> Node
  fromReachable res0 $ node |> modifyUnder src \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {dict = new_dict, target = res0})
      where
      new_wire = find_new_wire (curr, arr)
      new_dict = dict arr |> uncurry Map.insert new_wire

-- * Split Morphism, Object, Category

{- |
Partition the prefixes of a morphism.
It returns a partition of `prefix` of the given symbol, where the objects represented by
the elements in each group are unsplittable in the section category of the arrow specified
by `tgt`.

Examples:

>>> fmap (fmap symbol2) (partitionPrefix cone 2)
[[(1,1)],[(3,2)]]
-}
partitionPrefix :: Node e -> Symbol -> [[(Arrow e, Arrow e)]]
partitionPrefix node tgt =
  prefix node tgt
  |> concatMap (\(arr1, arr23) -> suffix (target arr1) (symbol arr23) |> fmap (arr1,))
  |> fmap (\(arr1, (arr2, arr3)) -> ((arr1, arr2 `join` arr3), (arr1 `join` arr2, arr3)))
  |> bipartiteEqclassOn symbol2 symbol2
  |> fmap fst
  |> fmap (sortOn symbol2)
  |> sortOn (fmap symbol2)

{- |
Split a symbol on a node.

Examples:

>>> printNode' $ fromJust $ splitMorphism (0,2) [0,1::Int] cone
- 0->1; 1->2
  - 0->1
- 0->3; 1->4; 2->8; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> printNode' $ fromJust $ splitMorphism (3,2) [0,1::Int] cone
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
  Eq k
  => (Symbol, Symbol)  -- ^ The symbols reference to the morphism to split.
  -> [k]               -- ^ The keys to classify splittable groups given by `partitionPrefix`.
  -> Node e            -- ^ The root node of BAC.
  -> Maybe (Node e)    -- ^ The result.
splitMorphism (src, tgt) splittable_keys node = do
  src_arr <- node |> arrow src
  guard $ root node |> locate tgt |> (== Inner)
  let splittable_groups = partitionPrefix (target src_arr) tgt |> fmap (fmap symbol2)
  guard $ length splittable_groups == length splittable_keys

  let src_syms = target src_arr |> symbols
  let splitted_syms =
        splittable_keys |> label 0 |> fmap (\i -> maximum src_syms * i + tgt)

  let res0 = Node do
        (value, arr) <- target src_arr |> edges
        let sym0 = symbol arr
        if sym0 == tgt
        then do
          r' <- splitted_syms
          let split (s, r) = if r == tgt then (s, r') else (s, r)
          let splitted_dict = dict arr |> Map.toList |> fmap split |> Map.fromList
          return (value, arr {dict = splitted_dict})
        else do
          let split (s, r) = if r == tgt then (s, r') else (s, r)
                where
                r' =
                  splittable_groups
                  |> findIndex ((sym0, s) `elem`)
                  |> fromJust
                  |> (splitted_syms !!)
          let splitted_dict = dict arr |> Map.toList |> fmap split |> Map.fromList
          return (value, arr {dict = splitted_dict})

  fromReachable res0 $ node |> modifyUnder src \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {dict = merged_dict, target = res0})
      where
      merge (s, r)
        | s == tgt  = [(s', r) | s' <- splitted_syms]
        | otherwise = [(s, r)]
      merged_dict = dict arr |> Map.toList |> concatMap merge |> Map.fromList

{- |
Partition symbols of a object.
It returns a partition of `symbols` of the given node, where the objects represented by
the elements in each group are unsplittable in the given bounded acyclic category.

Examples:

>>> partitionSymbols $ cone
[[1,2,3,4,6]]

>>> partitionSymbols $ target $ fromJust $ arrow 1 crescent
[[1,2,3],[5,6,7]]
-}
partitionSymbols :: Node e -> [[Symbol]]
partitionSymbols =
  arrows
  .> fmap (dict .> Map.elems)
  .> zip [0 :: Int ..]
  .> concatMap sequence
  .> bipartiteEqclass
  .> fmap (snd .> sort)
  .> sort

{- |
Split a node referenced by a symbol.

Examples:

>>> printNode' $ fromJust $ splitObject 1 [0,1::Int] crescent
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
  Eq k
  => Symbol          -- ^ The symbol referencing the node to be splitted.
  -> [k]             -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
splitObject tgt splittable_keys node = do
  guard $ root node |> locate tgt |> (== Inner)
  tgt_arr <- node |> arrow tgt
  res0 <- splitCategory splittable_keys (target tgt_arr)

  let splitSym :: [Symbol] -> Symbol -> [Symbol]
      splitSym syms s =
        splittable_keys |> label 0 |> fmap (\i -> maximum syms * i + s)

  fromInner $ node |> modifyUnder tgt \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {dict = duplicated_dict, target = res})
      where
      s_syms = target arr |> symbols
      r_syms = target curr |> symbols
      duplicate (s, r)
        | dict curr ! r == tgt = splitSym s_syms s `zip` splitSym r_syms r
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict arr |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      let r_syms = target curr |> symbols
      let splitted_syms = splitSym r_syms (symbol arr)
      (sym, res) <- splitted_syms `zip` res0
      let split (s, r)
            | s == base                    = Just (base, sym)
            | locate s (root res) == Inner = Just (s, r)
            | otherwise                    = Nothing
      let splitted_dict =
            dict arr |> Map.toList |> mapMaybe split |> Map.fromList
      return (value, arr {dict = splitted_dict, target = res})

{- |
Split a root node.

Examples:

>>> let crescent_1 = target $ fromJust $ arrow 1 crescent
>>> traverse_ printNode' $ fromJust $ splitCategory [0,1::Int] crescent_1
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
  Eq k
  => [k]             -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe [Node e]  -- ^ The list of the root nodes representing splitted categories.
splitCategory splittable_keys node = do
  let splittable_groups = partitionSymbols node
  guard $ length splittable_groups == length splittable_keys

  let splitted_groups =
        splittable_keys
        |> nub
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))

  return do
    group <- splitted_groups
    let splitted_edges =
          node |> edges |> filter (\(_, arr) -> symbol arr `elem` group)
    return $ Node splitted_edges

-- * Merge Morphisms, Objects, Categories

{- |
Merge symbols on a node.

Examples:

>>> printNode' $ fromJust $ mergeMorphisms (1,[2,3,6,8]) torus
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
  -> Node e           -- ^ The root node of BAC.
  -> Maybe (Node e)   -- ^ The result.
mergeMorphisms (src, tgts) node = do
  guard $ notNull tgts
  src_arr <- node |> arrow src
  tgt_arrs <- tgts |> traverse \tgt -> target src_arr |> arrow tgt
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  guard $
    src /= base
    || (tgt_arrs |> fmap (target .> arrows .> fmap dict) |> allSame)
  guard $ suffix node src |> all \(_, arr) -> tgts |> fmap (dict arr !) |> allSame

  let merge s = if s `elem` tgts then head tgts else s

  let res0 = Node do
        (value, arr) <- target src_arr |> edges
        let dict' = dict arr |> Map.toList |> fmap (second merge) |> Map.fromList
        return (value, arr {dict = dict'})

  fromReachable res0 $ node |> modifyUnder src \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {dict = dict', target = res0})
      where
      dict' = dict arr |> Map.toList |> fmap (first merge) |> Map.fromList

mergeObjects :: [Symbol] -> Node e -> Maybe (Node e)
mergeObjects tgts node = do
  guard $ notNull tgts
  let tgt = head tgts
  tgt_nodes <- tgts |> traverse (`arrow` node) |> fmap (fmap target)

  let tgt_pars = tgts |> fmap (suffixND node)

  guard $ tgt_pars |> fmap length |> allSame
  guard $ transpose tgt_pars |> all (fmap (fst .> symbol) .> allSame)

  sequence_ $ node |> foldUnder tgt \curr results -> do
    results' <- results |> traverse sequence

    let collapse = nubSort $ fmap sort do
          (lres, arr) <- results' `zip` arrows (target curr)
          case lres of
            AtOuter -> mzero
            AtInner res -> res |> fmap (fmap (dict arr !))
            AtBoundary ->
              transpose tgt_pars
              |> fmap (fmap symbol2)
              |> filter (head .> fst .> (== symbol curr))
              |> fmap (fmap snd)

    guard $ collapse |> concat |> anySame |> not

    return collapse

  let merged_node = mergeCategories tgt_nodes
  let merging_offsets = tgt_nodes |> fmap (symbols .> maximum) |> scanl (+) 0

  let nd_merged_dicts = Map.fromList do
        arr_arrs <- transpose tgt_pars
        let merged_wire =
              arr_arrs |> fmap (snd .> symbol) |> head |> (base,)
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
            (res, (value, arr)) <- results `zip` edges (target curr)
            let is_tgt = symbol (curr `join` arr) `elem` tgts
            let collapsed_node =
                  if is_tgt
                  then merged_node
                  else res |> fromInner |> fromMaybe (target arr)
            let collapsed_dict =
                  if is_tgt
                  then find_merged_dict (curr, arr)
                  else dict arr |> Map.filter (\sym -> dict curr ! sym `elem` tail tgts)
            return (value, arr {dict = collapsed_dict, target = collapsed_node})

      in Node collapsed_edges

{- |
Merge multiple nodes.

Examples:

>>> printNode' (mergeCategories [singleton (), singleton (), empty, singleton ()])
- 0->1
- 0->2
- 0->3

>>> printNode' (mergeCategories [singleton (), crescent])
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
mergeCategories :: [Node e] -> Node e
mergeCategories nodes = Node {edges = merged_edges}
  where
  offsets = nodes |> fmap (symbols .> maximum) |> scanl (+) 0
  merged_edges = do
    (offset, node) <- zip offsets nodes
    (value, arr) <- edges node
    let dict' = dict arr |> fmap (+ offset)
    return (value, arr {dict = dict'})

-- * Advanced Operations

trimObject :: Symbol -> Node e -> Maybe (Node e)
trimObject tgt node = do
  guard $ root node |> locate tgt |> (== Inner)
  tgt_arr <- node |> arrow tgt

  fromReachable (target tgt_arr) $ node |> modifyUnder tgt \(curr, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtBoundary -> do
      (subvalue, subarr) <- target arr |> edges
      let concated_dict = dict arr `cat` dict subarr
      return (subvalue, subarr {dict = concated_dict})
    AtInner res -> return (value, arr {dict = filtered_dict, target = res})
      where
      filtered_dict = dict arr |> Map.filter (\s -> dict curr ! s /= tgt)

insertMorphism :: (Symbol, Maybe Symbol) -> (e, e) -> Node e -> Maybe (Node e)
insertMorphism (src, tgt) (val1, val2) node = do
  src_arr <- node |> arrow src
  let new_sym = target src_arr |> symbols |> maximum |> (+ 1)
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- target src_arr |> arrow tgt
      let new_outdict = target tgt_arr |> symbols |> fmap (\s -> (s, s+1)) |> Map.fromList
      let new_outedge = (val2, Arrow {dict = new_outdict, target = target tgt_arr})
      let new_node = Node {edges = [new_outedge]}
      let new_indict = dict tgt_arr |> Map.mapKeys (+ 1) |> Map.insert base new_sym
      return (val1, Arrow {dict = new_indict, target = new_node})
    Nothing ->
      return (val1, Arrow {dict = Map.singleton base new_sym, target = empty})

  let res0 = Node $ edges (target src_arr) ++ [new_inedge]

  fromReachable res0 $ node |> modifyUnder src \(curr, (value, arr)) res ->
    case fromReachable res0 res of
      Nothing -> return (value, arr)
      Just res -> return (value, arr {dict = dict', target = res})
        where
        newSym syms = (+) (maximum syms + 1)
        s_syms = target curr |> symbols
        r_syms = target arr |> symbols
        dict' =
          dict arr
          |> Map.toList
          |> concatMap (\(s, r) ->
            if dict curr ! r == src
            then [(s, r), (newSym s_syms s, newSym r_syms r)]
            else [(s, r)]
          )
          |> Map.fromList

expandMergingSymbols :: Node e -> [[Symbol]] -> Maybe [[Symbol]]
expandMergingSymbols node =
  traverse (traverse (`arrow` node))
  .> fmap (
    zip [0 :: Integer ..]
    .> concatMap sequence
    .> fmap (fmap (dict .> Map.toList))
    .> concatMap sequence
    .> fmap (\(a, (b, c)) -> ((a, b), c))
    .> bipartiteEqclass
    .> fmap snd
    .> fmap sort
    .> sort
  )

mergeMorphismsAggressively :: Symbol -> [[Symbol]] -> Node e -> Maybe (Node e)
mergeMorphismsAggressively src tgts node = do
  src_arr <- node |> arrow src

  tgt_arrs <- tgts |> traverse (traverse (`arrow` target src_arr))
  guard $ tgt_arrs |> all (fmap target .> fmap root .> void .> allSame)

  let mergeSymbol tgts' s = tgts' |> filter (elem s) |> (++ [[s]]) |> head |> head

  merging_lists <- expandMergingSymbols (target src_arr) tgts
  let merged_node = Node do
        (value, arr) <- target src_arr |> edges
        let merged_dict = dict arr |> fmap (mergeSymbol merging_lists)
        return (value, arr {dict = merged_dict})
  let res0 = (merged_node, merging_lists)
  let merging_lists_of = fromReachable res0 .> fmap snd .> fromMaybe []

  located_res <- sequence $
    node |> foldUnder src \curr results -> do
      results' <- traverse sequence results
      merging_lists <-
        results'
        |> concatMap merging_lists_of
        |> zip (target curr |> arrows |> fmap dict)
        |> fmap (sequence .> fmap (uncurry (!)))
        |> expandMergingSymbols (target curr)
      let merged_node = Node do
            (res, (value, arr)) <- results' `zip` edges (target curr)
            let merged_dict =
                  dict arr
                  |> fmap (mergeSymbol merging_lists)
                  |> Map.mapKeys (mergeSymbol (merging_lists_of res))
            case fromReachable res0 res of
              Nothing -> return (value, arr {dict = merged_dict})
              Just (res, _) -> return (value, arr {dict = merged_dict, target = res})
      return (merged_node, merging_lists)

  fromReachable merged_node $ fmap fst located_res

