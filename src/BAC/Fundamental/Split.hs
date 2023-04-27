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
import Data.List.Extra (anySame)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>))

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
Partition the prefixes of a morphism.
It returns a partition of `prefix` of the given symbol, where the objects represented by
the elements in each group are unsplittable in the section category of the arrow specified
by `tgt`.

Examples:

>>> partitionPrefix cone 2
[[(1,1)],[(3,2)]]
-}
partitionPrefix :: BAC -> Symbol -> [[(Symbol, Symbol)]]
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
Split a symbol on a node (split a non-terminal morphism).

Examples:

>>> printBAC $ fromJust $ splitSymbol (0,2) [(2,[0]),(7,[1])] cone
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

>>> printBAC $ fromJust $ splitSymbol (3,2) [(5,[0]),(6,[1]),(7,[])] cone
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
  (Symbol, Symbol)      -- ^ The symbols reference to the morphism to split.
  -> [(Symbol, [Int])]  -- ^ The map from new symbols to indices of splittable groups
                        --   given by `partitionPrefix`.
  -> BAC
  -> Maybe BAC
splitSymbol (src, tgt) splitted_syms node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let splittable_groups = partitionPrefix (target src_arr) tgt
  guard $
    splitted_syms
    |> concatMap snd
    |> sort
    |> (== [0..length splittable_groups-1])
  guard $
    target src_arr
    |> symbols
    |> filter (/= tgt)
    |> (++ fmap fst splitted_syms)
    |> anySame
    |> not

  let splitter =
        splitted_syms
        |> concatMap sequence
        |> fmap (fmap (splittable_groups !!))
        |> concatMap sequence
        |> fmap swap
        |> Map.fromList

  let splitted_edges =
        splitted_syms
        |> fmap \(sym, _) ->
          dict tgt_subarr
          |> Map.insert base sym
          |> \splitted_dict -> tgt_subarr {dict = splitted_dict}

  let res0 = fromEdges $ splitted_edges ++ do
        edge <- target src_arr |> edges
        let sym0 = symbol edge
        guard $ sym0 /= tgt
        let split s r = Map.lookup (sym0, s) splitter |> fromMaybe r
        let splitted_dict = dict edge |> Map.mapWithKey split
        return edge {dict = splitted_dict}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = merged_dict, target = res0}
      where
      merge (s, r)
        | s == tgt  = [(s', r) | (s', _) <- splitted_syms]
        | otherwise = [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

-- | Split a symbol in the root node (split an initial morphism).
splitSymbolOnRoot :: Symbol -> [(Symbol, [Int])] -> BAC -> Maybe BAC
splitSymbolOnRoot tgt = splitSymbol (base, tgt)

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
Split a node (split a terminal morphism).

Examples:

>>> partition = [(makeShifter crescent 0, [0]), (makeShifter crescent 1, [1])]
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

>>> partition' = [(makeShifter cone 0, [0,1]), (makeShifter cone 1, [])]
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
  Symbol     -- ^ The symbol referencing the node to be splitted.
  -> [((Symbol, Symbol) -> Symbol, [Int])]
             -- ^ The splitters and indices of splittable groups of symbols given by
             --   `partitionSymbols`.
  -> BAC
  -> Maybe BAC
splitNode tgt partition node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  let splitter = partition |> fmap fst |> sequence
  guard $
    arrowsUnder node tgt
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> concatMap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  res0 <-
    target tgt_arr
    |> splitRootNode (fmap snd partition)

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      duplicate (s, r)
        | dict curr ! r == tgt = splitter (symbol (curr `join` edge), s)
                                 `zip` splitter (symbol curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      (res, sym) <- res0 `zip` splitter (symbol curr, symbol edge)
      let split (s, r)
            | s == base                    = Just (base, sym)
            | locate (root res) s == Inner = Just (s, r)
            | otherwise                    = Nothing
      let splitted_dict =
            dict edge |> Map.toList |> mapMaybe split |> Map.fromList
      return edge {dict = splitted_dict, target = res}

{- |
Split a root node (split a BAC).

Examples:

>>> import Data.Foldable (traverse_)
>>> crescent_1 = target $ fromJust $ arrow crescent 1
>>> traverse_ printBAC $ fromJust $ splitRootNode [[0],[1]] crescent_1
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
  [[Int]]  -- ^ The indices of splittable groups of symbols given by `partitionSymbols`.
  -> BAC
  -> Maybe [BAC]
splitRootNode partition node = do
  let splittable_groups = partitionSymbols node
  guard $ partition |> concat |> sort |> (== [0..length splittable_groups-1])

  return do
    indices <- partition
    let group = indices |> concatMap (splittable_groups !!)
    let splitted_edges = node |> edges |> filter (symbol .> (`elem` group))
    return $ fromEdges splitted_edges
