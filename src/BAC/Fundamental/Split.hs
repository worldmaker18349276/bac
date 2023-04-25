{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Split (
  partitionPrefix,
  partitionSymbols,
  makeSplitter,
  splitSymbol,
  splitSymbolOnRoot,
  splitNode,
  splitRootNode,

  splitSymbolMutation,
  splitSymbolOnRootMutation,
  splitNodeMutation,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.List (sort)
import Data.List.Extra (anySame)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe, fromMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)
import Numeric.Natural (Natural)

import BAC.Base
import BAC.Fundamental.Mutation
import BAC.Fundamental.Restructure
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
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
- 0->3; 1->4; 2->7; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> printBAC $ fromJust $ splitSymbol (3,2) [(5,[0]),(6,[1])] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 3->6; 4->4; 5->2; 6->2
  - 0->1; 1->5; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->6; 2->3
    *1
-}
splitSymbol ::
  (Symbol, Symbol)      -- ^ The symbols reference to the morphism to split.
  -> [(Symbol, [Int])]  -- ^ The map from new symbols to indices of splittable groups
                        --   given by `partitionPrefix`.
  -> BAC
  -> Maybe BAC
splitSymbol (src, tgt) splitted_syms node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
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

  node <- addEdge (src, tgt) node

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let sym0 = symbol edge
        if sym0 == tgt
        then do
          (sym, _) <- splitted_syms
          let splitted_dict = dict edge |> Map.insert base sym
          return edge {dict = splitted_dict}
        else do
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

splitSymbolMutation :: (Symbol, Symbol) -> [(Symbol, [Int])] -> BAC -> [Mutation]
splitSymbolMutation (src, tgt) splitted_syms node =
  [Duplicate (src, tgt) (fmap (src,) syms) | tgt `elem` prefixes]
  |> if src == base then (++ root_mutation) else id
  where
  prefixes =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
  syms = fmap fst splitted_syms
  root_mutation = prefixes |> fmap \s -> Duplicate (src, s) (fmap (,s) syms)

-- | Split a symbol in the root node (split an initial morphism).
splitSymbolOnRoot :: Symbol -> [(Symbol, [Int])] -> BAC -> Maybe BAC
splitSymbolOnRoot tgt = splitSymbol (base, tgt)

splitSymbolOnRootMutation :: Symbol -> [(Symbol, [Int])] -> BAC -> [Mutation]
splitSymbolOnRootMutation tgt = splitSymbolMutation (base, tgt)

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

makeSplitter :: BAC -> [Natural] -> (Symbol, Symbol) -> [Symbol]
makeSplitter node offsets (src, tgt) = do
  let ran = arrow node src |> fromJust |> target |> symbols |> maximum
  offset <- offsets
  return $ ran * offset + tgt

{- |
Split a node (split a terminal morphism).

Examples:

>>> splitter = makeSplitter crescent [0,1]
>>> partition = [(splitter .> (!! 0), [0]), (splitter .> (!! 1), [1])]
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
        | dict curr ! r == tgt = splitter (symbol (curr `join` edge), s) `zip` splitter (symbol curr, r)
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

splitNodeMutation ::
  Ord k
  => Symbol
  -> [k]
  -> ((Symbol, Symbol) -> Map k Symbol)
  -> BAC
  -> [Mutation]
splitNodeMutation tgt splittable_keys splitter node =
  incoming_mutation ++ outgoing_mutation
  where
  incoming_mutation =
    suffix node tgt
    |> fmap symbol2
    |> fmap \(s1, s2) ->
      splitter (s1, s2) |> Map.elems |> fmap (s1,) |> Duplicate (s1, s2)
  splittable_groups =
    splittable_keys `zip` partitionSymbols node
    |> concatMap sequence
    |> fmap swap
    |> Map.fromList
  outgoing_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> id &&& fmap (\s -> splittable_groups ! s |> (splitter (tgt, s) !))
    |> both (fmap (tgt,))
    |> uncurry Transfer
    |> (: [])

{- |
Split a root node (split a BAC).

Examples:

>>> let crescent_1 = target $ fromJust $ arrow crescent 1
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
