{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module BAC.Fundamental.Split (
  partitionPrefix,
  partitionSymbols,
  splitSymbol,
  splitSymbolOnRoot,
  splitNode,
  splitRootNode,
) where

import Control.Monad (guard)
import Data.List (sort)
import Data.List.Extra (anySame, disjoint, replace)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>))

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)

{- |
Partition the prefixes of an arrow.  It returns a partition of @prefix node tgt@ excluding
@(tgt, base)@.  The objects represented by the elements in each group are unsplittable in
the section category of the arrow specified by `tgt`.

Examples:

>>> partitionPrefix cone 2
[[(1,1)],[(3,2)]]

>>> partitionPrefix (target $ fromJust $ arrow cone 3) 2
[[(1,1)],[(4,1)]]
-}
partitionPrefix :: BAC -> Symbol -> [[(Symbol, Symbol)]]
partitionPrefix node tgt =
  prefix node tgt
  -- suffix decomposition: `arr23` => `(arr2, arr3)`
  |> concatMap (\(arr1, arr23) -> suffix (target arr1) (symbol arr23) |> fmap (arr1,))
  -- connect prefix and suffix
  |> fmap (\(arr1, (arr2, arr3)) -> ((arr1, arr2 `join` arr3), (arr1 `join` arr2, arr3)))
  |> fmap (both symbol2)
  -- classify prefixes by connectivity
  |> bipartiteEqclass
  |> fmap fst
  |> fmap sort
  |> sort

-- | Ckeck if `partition1` is finer than `partition2`: if two elements are in the same
--   part in `partition1`, they are also in the same part in `partition2`.
finer :: Ord a => [[a]] -> [[a]] -> Bool
finer partition1 partition2 = isPartition && sameHost && include
  where
  isPartition = concat partition1 |> anySame |> not
  sameHost = sort (concat partition1) == sort (concat partition2)
  include =
    partition1
    |> all \group ->
      partition2
      |> all \group' ->
        group `disjoint` group' || group `subset` group'
  subset a b = a |> all (`elem` b)

{- |
Split a symbol on a node, with two parameters @(src, tgt) :: (Symbol, Symbol)@ and
@partition :: Map Symbol [(Symbol, Symbol)]@.  `src` indicates the node to operate, `tgt`
indicates the symbol to split, and `partition` is a list of splitted symbols and the
corresponding group of splitted prefixes, which should be an union of some groups given by
`partitionPrefix`.  If there is a splitted symbol which has an empty group, it will become
a nondecomposable symbol.  For simplicity, the direct edges to the splitted symbols will
always be constructed.

In categorical perspectives, it splits a non-terminal morphism, where @(src, tgt)@
indicates a proper morphism to split, and @(src, sym)@ for all @(sym, grps) <- partition@
will indicate a splitted morphism, and the morphism chains in the group `grps` will
compose to this morphism.  A splitted morphism which no morphism chains compose to is
nondecomposable.

Examples:

>>> let partition_cone02 = [(2,[(1,1)]),(7,[(3,2)])]
>>> printBAC $ fromJust $ splitSymbol (0,2) partition_cone02 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->2
  *0
- 0->3; 1->4; 2->7; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      &2
    - 0->2
  - 0->4; 1->2; 2->3
    *1
- 0->7
  *2

>>> let partition_cone32 = [(5,[(1,1)]),(6,[(4,1)]),(7,[])]
>>> printBAC $ fromJust $ splitSymbol (3,2) partition_cone32 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 3->6; 4->4; 5->2; 6->2; 7->2
  - 0->1; 1->5; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->6; 2->3
    *1
  - 0->5
    *0
  - 0->6
    *0
  - 0->7
    *0
-}
splitSymbol ::
  (Symbol, Symbol)
  -- ^ The pair of symbols referencing the arrow to split.
  -> [(Symbol, [(Symbol, Symbol)])]
  -- ^ The map from new symbols to splitted groups finer than `partitionPrefix`.
  -> BAC
  -> Maybe BAC
splitSymbol (src, tgt) partition node = do
  -- ensure that `(src, tgt)` is reachable and proper
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  guard $ tgt /= base
  let src_node = target src_arr

  -- ensure that every splittable groups have been classified to splitted symbols
  let splittable_groups = partitionPrefix src_node tgt
  guard $ splittable_groups `finer` fmap snd partition

  -- validate splitted symbols
  guard $ src_node |> symbols |> replace [tgt] (fmap fst partition) |> anySame |> not

  -- classify each prefix to a splitted symbol
  let splitter =
        partition
        |> concatMap sequence
        |> fmap swap
        |> Map.fromList

  let src_node' = fromEdges do
        -- add a direct edge to `tgt`, then modify their dictionaries
        edge <- src_node |> edges |> (tgt_subarr :)
        let sym0 = symbol edge
        if sym0 == tgt
        then do
          -- duplicate the direct edge for each splitted symbol
          (sym, _) <- partition
          let duplicated_dict = dict tgt_subarr |> Map.insert base sym
          return edge {dict = duplicated_dict}
        else do
          -- modify the dictionary of the edge for corresponding splitted symbol
          let split s r = Map.lookup (sym0, s) splitter |> fromMaybe r
          let splitted_dict = dict edge |> Map.mapWithKey split
          return edge {dict = splitted_dict}

  fromReachable src_node' $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {dict = merged_dict, target = src_node'}
      where
      -- map splitted symbols like before splitting
      merge (s, r)
        | s == tgt  = [(s', r) | (s', _) <- partition]
        | otherwise = [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

-- | Split a symbol on the root node (split an initial morphism).  See `splitSymbol` for
--   details.
splitSymbolOnRoot :: Symbol -> [(Symbol, [(Symbol, Symbol)])] -> BAC -> Maybe BAC
splitSymbolOnRoot tgt = splitSymbol (base, tgt)

{- |
Partition symbols on a node.
It returns a partition of `symbols` of the given node excluding `base`, where the objects
represented by the elements in each group are unsplittable in the given bounded acyclic
category.

Examples:

>>> partitionSymbols $ cone
[[1,2,3,4,6]]

>>> partitionSymbols $ target $ fromJust $ arrow cone 4
[[1],[2]]

>>> partitionSymbols $ target $ fromJust $ arrow crescent 1
[[1,2,3],[5,6,7]]
-}
partitionSymbols :: BAC -> [[Symbol]]
partitionSymbols =
  edges
  .> fmap (dict .> Map.elems)
  .> zip [0 :: Int ..]
  .> concatMap sequence
  .> bipartiteEqclass
  .> fmap (snd .> sort)
  .> sort

{- |
Split a node, with parameters @tgt :: Symbol@, the symbol of the node to split, and
@partition :: [((Symbol, Symbol) -> Symbol, [Int])]@, list of splitter functions and
indices to splittable groups given by `partitionSymbols`.

In categorical perspectives, it splits a terminal morphism, where `tgt` indicates the
source object of morphism to split.  For all incoming morphisms of this object, say
@(s1, s2)@, the pair of symbol @(s1, splitter (s1, s2))@ for @(splitter, _) <- partition@
will indicate the incoming morphism of splitted object with the same source object.

Examples:

>>> partition = [(makeShifter crescent 0, [1,2,3]), (makeShifter crescent 1, [5,6,7])]
>>> printBAC $ fromJust $ splitNode 1 partition crescent
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

>>> partition' = [(makeShifter cone 0, [1,2]), (makeShifter cone 1, [])]
>>> printBAC $ fromJust $ splitNode 4 partition' cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->10; 8->10
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
  - 0->5
    &2
  - 0->8
    *2
-}
splitNode ::
  Symbol
  -- ^ The symbol referencing the node to be splitted.
  -> [((Symbol, Symbol) -> Symbol, [Symbol])]
  -- ^ The splitters and splitted groups of symbols finer than `partitionSymbols`.
  -> BAC
  -> Maybe BAC
splitNode tgt partition node = do
  -- ensure that `tgt` is reachable and proper
  tgt_node <- arrow node tgt |> fmap target
  guard $ tgt /= base

  let splitter = partition |> fmap fst |> sequence
  -- validate `splitter`
  guard $
    arrowsUnder node tgt
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> concatMap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  -- split `tgt_node`
  tgt_nodes' <- tgt_node |> splitRootNode (fmap snd partition)

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {dict = duplicated_dict, target = subnode}
      where
      -- duplicate links of the base wire of the node of `tgt`
      duplicate (s, r)
        | dict curr ! r == tgt = splitter (symbol (curr `join` edge), s)
                                 `zip` splitter (symbol curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      -- split incoming edges of the node of `tgt`
      let splitted_syms = splitter (symbol curr, symbol edge)
      (tgt_node', sym) <- tgt_nodes' `zip` splitted_syms
      let splitted_dict =
            dict edge
            |> Map.filterWithKey (\s _ -> s `elem` symbols tgt_node')
            |> Map.insert base sym
      return edge {dict = splitted_dict, target = tgt_node'}

{- |
Split a root node (split a BAC), with a parameter @partition :: [[Int]]@, which are
indices to splittable groups representing each splitted category.

Examples:

>>> import Data.Foldable (traverse_)
>>> crescent_1 = target $ fromJust $ arrow crescent 1
>>> traverse_ printBAC $ fromJust $ splitRootNode [[1,2,3],[5,6,7]] crescent_1
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
splitRootNode ::
  [[Symbol]]
  -- ^ The splitted groups of symbols finer than `partitionSymbols`.
  -> BAC
  -> Maybe [BAC]
splitRootNode partition node = do
  -- ensure that every splittable groups have been classified to splitted symbols
  let splittable_groups = partitionSymbols node
  guard $ splittable_groups `finer` partition

  return do
    group <- partition
    let splitted_edges = node |> edges |> filter (symbol .> (`elem` group))
    return $ fromEdges splitted_edges
