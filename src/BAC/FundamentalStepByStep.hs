{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.FundamentalStepByStep (
  removeNDSymbolOnRoot',
  removeLeafNode',

  duplicateNDSymbol',
  duplicateNode',
) where

import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.List (findIndex, transpose)
import Data.List.Extra (allSame, anySame, notNull, groupSortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

import BAC.Base
import BAC.Fundamental
import Utils.Utils ((.>), (|>), foldlMUncurry)

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
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

  let keys = partitionSymbols node |> zip [0..] |> groupSortOn (snd .> elem tgt) |> fmap (fmap fst)
  return $ node |> splitRootNode keys |> fromJust |> head

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
        arrowsUnder node tgt
        |> concatMap ((id &&& (`divide` tgt_arr)) .> sequence .> fmap symbol2)
        |> filter (fst .> (/= base))

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let (add_list, []) = node |> missingAltPathsOfArrow sym2 |> fromJust
    node <- (node, add_list) |> foldlMUncurry \(node, add_edge) -> do
      return $ node |> addEdge add_edge |> fromJust

    return $ node |> removeNDSymbol sym2 |> fromJust

  let keys = partitionSymbols node |> zip [0..] |> groupSortOn (snd .> elem tgt) |> fmap (fmap fst)
  return $ node |> splitRootNode keys |> fromJust |> head


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
  let arrs = arrowsUnder node tgt
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
        arrowsUnder node tgt
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
          |> fmap (\splittable_prefix ->
            splitted_prefixes
            |> findIndex (elem splittable_prefix)
            |> fromJust
            |> (splitted_symbols !!)
          )
          |> (`zip` [0..])
          |> groupSortOn fst
          |> fmap (head .> fst &&& fmap snd)

    node |> splitSymbol (s1, s2) syms

