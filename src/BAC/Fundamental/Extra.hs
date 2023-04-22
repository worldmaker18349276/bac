{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Extra (
  removeNDSymbolOnRoot',
  removeLeafNode',

  duplicateNDSymbol',
  duplicateNode',

  removePrefix,
  removeSuffix,

  duplicatePrefix,
  duplicateSuffix,

  expandMergingSymbols,
  mergeSymbolsAggressively,
) where

import Control.Arrow (first, (&&&))
import Control.Monad (guard)
import Data.Foldable (find)
import Data.List (findIndex, sort, transpose)
import Data.List.Extra (allSame, anySame, notNull)
import Data.Map ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)

import BAC.Base
import BAC.Fundamental
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>), foldlMUncurry, guarded)

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
>>> printBAC $ fromJust $ removeNDSymbolOnRoot' 3 cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
-}
removeNDSymbolOnRoot' :: Symbol -> BAC -> Maybe BAC
removeNDSymbolOnRoot' tgt node = do
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


removePrefix :: (Symbol, Symbol) -> BAC -> Maybe BAC
removePrefix (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let remove_list = arrowsUnder tgt src_node |> fmap symbol |> filter (/= base) |> (tgt :)

  let res0 =
        target src_arr
        |> edges
        |> filter (dict .> notElem tgt)
        |> fromEdges
  let syms0 = symbols res0
  guard $ symbols src_node |> filter (`notElem` remove_list) |> (== syms0)

  fromReachable res0 $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner res -> return edge {target = res}
      AtBoundary -> return edge {dict = dict', target = res0}
        where
        dict' = dict edge |> Map.filterWithKey \s _ -> s `elem` syms0

removeSuffix :: (Symbol, Symbol) -> BAC -> Maybe BAC
removeSuffix (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let tgt_arr = src_arr `join` tgt_subarr
  let tgt' = symbol tgt_arr
  let tgt_node = target tgt_subarr

  lres <- sequence $
    node |> foldUnder tgt' \curr results -> do
      let is_outside = null (src_arr `divide` curr)
      let remove_list = if is_outside then [] else curr `divide` tgt_arr |> fmap symbol

      results' <- traverse sequence results

      let res = fromEdges do
            (lres, edge) <- results' `zip` edges (target curr)
            case lres of
              AtOuter -> return edge
              AtBoundary -> guarded (const is_outside) edge
              AtInner res ->
                if null (src_arr `divide` (curr `join` edge))
                then return edge {target = res}
                else return edge {dict = dict', target = res}
                where
                dict' = target edge |> symbols |> foldr Map.delete (dict edge)

      guard $ symbols (target curr) |> filter (`notElem` remove_list) |> (== symbols res)

      return res

  fromReachable tgt_node lres


duplicatePrefix :: (Symbol, Symbol) -> (Symbol -> [Symbol]) -> BAC -> Maybe BAC
duplicatePrefix (src, tgt) splitter node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let dup_list = arrowsUnder tgt src_node |> fmap symbol |> filter (/= base) |> (tgt :)

  let len = splitter tgt |> length
  guard $ len /= 0
  guard $ dup_list |> fmap splitter |> fmap length |> all (== len)
  guard $
    symbols src_node
    |> filter (`notElem` dup_list)
    |> (++ concatMap splitter dup_list)
    |> anySame
    |> not

  let res0 = fromEdges do
        edge <- edges (target src_arr)
        if symbol edge `notElem` dup_list
        then return edge
        else do
          dict' <-
            dict edge
            |> fmap (\sym ->
              if sym `elem` dup_list
              then splitter sym
              else replicate len sym
            )
            |> Map.toList
            |> fmap sequence
            |> transpose
            |> fmap Map.fromList
          return edge {dict = dict'}

  fromReachable res0 $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner res -> return edge {target = res}
      AtBoundary -> return edge {dict = dict', target = res0}
        where
        dict' =
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if s `elem` dup_list then [(s', r) | s' <- splitter s] else [(s, r)])
          |> Map.fromList

duplicateSuffix :: (Symbol, Symbol) -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateSuffix (src, tgt) splitter node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let len = splitter (src, tgt) |> length

  guard $ len /= 0
  guard $
    arrowsUnder tgt src_node
    |> all \arr ->
      let
        dup_list = arr `divide` tgt_subarr |> fmap symbol
        dup_syms = dup_list |> fmap (symbol arr,) |> fmap splitter
        same_len = dup_syms |> fmap length |> all (== len)
      in
        target arr
        |> symbols
        |> filter (`notElem` dup_list)
        |> (++ concat dup_syms)
        |> anySame
        |> not
        |> (same_len &&)

  let tgt_arr = src_arr `join` tgt_subarr
  let tgt' = symbol tgt_arr

  fromInner $
    node |> modifyUnder tgt' \(curr, edge) lres -> do
      let is_outside = null (src_arr `divide` curr)
      let sym = symbol curr
      let sym' = symbol (curr `join` edge)
      let dup_list' = (curr `join` edge) `divide` tgt_arr |> fmap symbol

      case lres of
        AtOuter -> return edge
        AtBoundary -> do
          guard $ not is_outside
          sym <- splitter (symbol curr, symbol edge)
          let dict' = dict edge |> Map.insert base sym
          return edge {dict = dict'}
        AtInner res ->
          if null (src_arr `divide` (curr `join` edge))
          then return edge {target = res}
          else if is_outside
          then
            dict edge
            |> Map.toList
            |> concatMap (\(s, r) ->
              if s `elem` dup_list'
              then splitter (sym', s) |> fmap (,r)
              else [(s, r)]
            )
            |> Map.fromList
            |> \dict' -> return edge {dict = dict', target = res}

          else
            dict edge
            |> Map.toList
            |> fmap (\(s, r) ->
              if s == base
              then replicate len base `zip` splitter (sym, symbol edge)
              else if s `elem` dup_list'
              then splitter (sym', s) `zip` splitter (sym, r)
              else replicate len (s, r)
            )
            |> transpose
            |> fmap Map.fromList
            |> fmap \dict' -> edge {dict = dict', target = res}


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

