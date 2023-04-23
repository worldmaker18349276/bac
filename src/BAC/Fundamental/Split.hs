{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

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
import Data.Bifunctor (Bifunctor (first, second))
import Data.List (elemIndices, findIndex, nub, sort)
import Data.List.Extra (anySame, nubSort, groupOnKey)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)
import Numeric.Natural (Natural)

import BAC.Base
import BAC.Fundamental.Mutation
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

>>> printBAC $ fromJust $ splitSymbol (0,2) [2,7] cone
- 0->1; 1->2
  - 0->1
- 0->3; 1->4; 2->7; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> printBAC $ fromJust $ splitSymbol (3,2) [5,6] cone
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
  (Symbol, Symbol)  -- ^ The symbols reference to the morphism to split.
  -> [Symbol]       -- ^ The new symbols of splittable groups given by `partitionPrefix`.
  -> BAC
  -> Maybe BAC
splitSymbol (src, tgt) splitted_syms node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let splittable_groups = partitionPrefix (target src_arr) tgt
  guard $ length splittable_groups == length splitted_syms
  guard $ target src_arr |> symbols |> filter (/= tgt) |> any (`elem` splitted_syms) |> not

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

splitSymbolMutation :: (Symbol, Symbol) -> [Symbol] -> BAC -> [Mutation]
splitSymbolMutation (src, tgt) splitted_syms node =
  [Duplicate (src, tgt) (fmap (src,) syms) | is_edge]
  |> if src == base then (++ root_mutation) else id
  where
  is_edge =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> elem tgt
  syms = nub splitted_syms
  splittable_groups = arrow node src |> fromJust |> target |> (`partitionPrefix` tgt)
  splitted_groups =
    splitted_syms `zip` splittable_groups
    |> groupOnKey fst
    |> fmap (second (concatMap snd))
  root_mutation =
    splitted_groups
    |> fmap \(sym, group) ->
      Transfer group (fmap (first (const sym)) group)

-- | Split a symbol in the root node (split an initial morphism).
splitSymbolOnRoot :: Symbol -> [Symbol] -> BAC -> Maybe BAC
splitSymbolOnRoot tgt = splitSymbol (base, tgt)

splitSymbolOnRootMutation :: Symbol -> [Symbol] -> BAC -> [Mutation]
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

>>> keys = [0::Natural,1]
>>> splitter = makeSplitter crescent keys .> zip keys .> fromList
>>> printBAC $ fromJust $ splitNode 1 keys splitter crescent
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
  Ord k
  => Symbol  -- ^ The symbol referencing the node to be splitted.
  -> [k]     -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> ((Symbol, Symbol) -> Map k Symbol)
  -> BAC
  -> Maybe BAC
splitNode tgt splittable_keys splitter node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  let splitted_keys = splittable_keys |> nubSort
  let arrs = arrowsUnder node tgt
  guard $
    arrs
    |> concatMap ((id &&& (`divide` tgt_arr)) .> sequence .> fmap symbol2)
    |> all (splitter .> Map.keys .> (== splitted_keys))
  guard $
    arrs
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> fmap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) |> Map.elems else [s1])
      |> anySame
      |> not

  res0 <-
    arrow node tgt
    |> fromJust
    |> target
    |> splitRootNode splittable_keys
    |> fmap Map.elems
  let splitter' = first symbol .> splitter .> Map.elems

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      duplicate (s, r)
        | dict curr ! r == tgt = splitter' (curr `join` edge, s) `zip` splitter' (curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      (res, sym) <- res0 `zip` splitter' (curr, symbol edge)
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
      Duplicate (s1, s2) (splitter (s1, s2) |> Map.elems |> fmap (s1,))
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
>>> traverse_ printBAC $ fromJust $ splitRootNode [False,True] crescent_1
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
  Ord k
  => [k]  -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> BAC
  -> Maybe (Map k BAC)
splitRootNode splittable_keys node = do
  let splittable_groups = partitionSymbols node
  guard $ length splittable_groups == length splittable_keys

  let splitted_keys = splittable_keys |> nub
  let splitted_groups =
        splitted_keys
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))

  return $ Map.fromList do
    (key, group) <- splitted_keys `zip` splitted_groups
    let splitted_edges = node |> edges |> filter (symbol .> (`elem` group))
    return (key, fromEdges splitted_edges)
