{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Extra (
  removeRootNDSymbol',
  removeLeafNode',

  duplicateNDSymbol',
  duplicateNode',

  expandMergingSymbols,
  mergeSymbolsAggressively,
) where

import Control.Arrow (first, (&&&))
import Control.Monad (guard)
import Data.Foldable (find)
import Data.List (sort, findIndex, transpose)
import Data.List.Extra (allSame, anySame, notNull)
import Data.Map ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)

import BAC.Base
import BAC.Fundamental
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>), foldlMUncurry)

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
Remove a nondecomposable symbol in the root node step by step (remove a nondecomposable
initial morphism step by step: removing all related morphisms, then splitting category).

Examples:

>>> cone' = fromJust $ addEdge (0,4) cone
>>> printBAC $ fromJust $ removeRootNDSymbol' 3 cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
-}
removeRootNDSymbol' :: Symbol -> BAC -> Maybe BAC
removeRootNDSymbol' tgt node = do
  guard $ nondecomposable node tgt
  guard $
    missingAltPathsOfArrow (0, tgt) node
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
    let ([], add_list') = node |> missingAltPathsOfArrow sym2 |> fromJust
    node <- (node, add_list') |> foldlMUncurry \(node, add_edge) -> do
      return $ node |> addEdge add_edge |> fromJust

    return $ node |> removeNDSymbol sym2 |> fromJust

  let keys = partitionSymbols node |> fmap (elem tgt)
  return $ node |> splitRootNode keys |> fromJust |> (! False)

{- |
Remove an leaf node step by step (remove a nondecomposable terminal morphism step by step:
removing all related morphisms, then splitting category).

Examples:

>>> printBAC $ fromJust $ removeLeafNode' 6 cone
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

>>> printBAC $ fromJust $ removeLeafNode' 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0

>>> removeLeafNode' 4 cone
Nothing
-}
removeLeafNode' :: Symbol -> BAC -> Maybe BAC
removeLeafNode' tgt node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  guard $ tgt_arr |> target |> edges |> null

  let remove_list =
        node
        |> arrowsUnder tgt
        |> concatMap ((id &&& (`divide` tgt_arr)) .> sequence .> fmap symbol2)
        |> filter (fst .> (/= base))

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let (add_list, []) = node |> missingAltPathsOfArrow sym2 |> fromJust
    node <- (node, add_list) |> foldlMUncurry \(node, add_edge) -> do
      return $ node |> addEdge add_edge |> fromJust

    return $ node |> removeNDSymbol sym2 |> fromJust

  let keys = partitionSymbols node |> fmap (elem tgt)
  return $ node |> splitRootNode keys |> fromJust |> (! False)


-- | Duplicate a nondecomposable symbol in a node step by step (duplicate a non-terminal
--   nondecomposable morphism step by step).
duplicateNDSymbol' :: (Symbol, Symbol) -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbol' (src, tgt) syms node = do
  guard $ notNull syms
  src_arr <- arrow node src
  let src_node = target src_arr
  guard $ locate (root src_node) tgt == Inner
  guard $ nondecomposable src_node tgt
  guard $
    src_node
    |> symbols
    |> filter (/= tgt)
    |> (syms ++)
    |> anySame
    |> not

  let arrSS = arrow2 node .> fromJust .> snd
  let joinSS ss1 ss2 = (fst ss1, symbol (arrSS ss1 `join` arrSS ss2))
  let tgt' = (base, src) `joinSS` (src, tgt) |> snd
  let angs = node |> findValidCoanglesAngles src tgt' |> fromJust
  let src_alts =
        fst angs
        |> fmap ((findIndex \(ss1, ss2) -> ss1 `joinSS` (src, tgt) == ss2) .> fromJust)
  let tgt_alts =
        snd angs
        |> fmap ((findIndex \(ss1, ss2) -> (src, tgt) `joinSS` ss1 == ss2) .> fromJust)

  node <- (node, filter (/= tgt) syms) |> foldlMUncurry \(node, sym) ->
    node |> addNDSymbol src tgt' sym src_alts tgt_alts

  if tgt `elem` syms
  then return node
  else node |> removeNDSymbol (src, tgt)

{- |
Duplicate a node step by step (duplicate an object step by step).

Examples:

>>> printBAC $ fromJust $ duplicateNode' 3 (makeSplitter crescent [0,1]) crescent
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
duplicateNode' :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateNode' tgt splitter node = do
  guard $ locate (root node) tgt |> (== Inner)
  let arrs = arrowsUnder tgt node
  guard $
    arrs
    |> concatMap (\arr ->
      arr
      |> dict
      |> Map.toList
      |> filter (snd .> (== tgt))
      |> fmap (fst .> (symbol arr,) .> splitter .> length)
    )
    |> allSame
  guard $
    arrs
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> fmap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  let tgt_subarr = arrow node tgt |> fromJust
  let dup_list = suffixND node tgt |> fmap symbol2
  let split_list =
        node
        |> arrowsUnder tgt
        |> concatMap (\arr -> arr `divide` tgt_subarr |> fmap (arr,))
        |> fmap symbol2
        |> filter (`notElem` dup_list)

  let origin_node = node

  node <- (node, dup_list) |> foldlMUncurry \(node, (s1, s2)) -> do
    let syms = splitter (s1, s2)
    node |> duplicateNDSymbol' (s1, s2) syms

  (node, split_list) |> foldlMUncurry \(node, (s1, s2)) -> do
    let src_arr_origin = arrow origin_node s1 |> fromJust
    let splitted_prefixes =
          prefix (target src_arr_origin) s2
          |> fmap (\(a1, a2) ->
            splitter (symbol (src_arr_origin `join` a1), symbol a2)
            |> fmap (symbol a1,)
          )
          |> transpose

    let src_arr = arrow node s1 |> fromJust
    let splitted_symbols = splitter (s1, s2)

    let syms =
          partitionPrefix (target src_arr) s2
          |> fmap head
          |> fmap \splittable_prefix ->
            splitted_prefixes
            |> findIndex (elem splittable_prefix)
            |> fromJust
            |> (splitted_symbols !!)

    node |> splitSymbol (s1, s2) syms


expandMergingSymbols :: BAC -> [[Symbol]] -> [[Symbol]]
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

mergeSymbolsAggressively ::
  (Symbol, [[Symbol]]) -> ((Symbol, [Symbol]) -> Symbol) -> BAC -> Maybe BAC
mergeSymbolsAggressively (src, tgts) merger node = do
  src_arr <- arrow node src

  tgt_arrs <- tgts |> traverse (traverse (arrow (target src_arr)))
  guard $ tgt_arrs |> all (fmap target .> allSame)

  let validateMerger curr merging_lists =
        target curr
        |> symbols
        |> filter (`notElem` concat merging_lists)
        |> (++ fmap ((symbol curr,) .> merger) merging_lists)
        |> anySame
        |> not

  let merging_lists = expandMergingSymbols (target src_arr) tgts
  guard $ validateMerger src_arr merging_lists

  let mergeSymbol (src', tgts') s = tgts' |> find (elem s) |> maybe s ((src',) .> merger)
  let merged_node = fromEdges do
        edge <- target src_arr |> edges
        let merged_dict = dict edge |> fmap (mergeSymbol (src, merging_lists))
        return edge {dict = merged_dict}
  let res0 = (merged_node, merging_lists)

  lres <- sequence $
    node |> foldUnder src \curr results -> do
      let sym0 = symbol curr
      results' <-
        traverse sequence results
        |> fmap (fmap (fromReachable res0 .> maybe (Nothing, []) (first Just)))
      let merging_lists =
            target curr
            |> edges
            |> fmap dict
            |> (`zip` fmap snd results')
            |> concatMap (sequence .> fmap (sequence .> fmap (uncurry (!))))
            |> expandMergingSymbols (target curr)
      guard $ validateMerger curr merging_lists

      let merged_node = fromEdges do
            ((lres, merging_lists'), edge) <- results' `zip` edges (target curr)
            let sym = symbol (curr `join` edge)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol (sym0, merging_lists))
                  |> Map.mapKeys (mergeSymbol (sym, merging_lists'))
            let res = fromMaybe (target edge) lres
            return edge {dict = merged_dict, target = res}
      return (merged_node, merging_lists)

  fromReachable res0 lres |> fmap fst

