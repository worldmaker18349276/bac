{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Duplicate (
  duplicateNDSymbol,
  duplicateNode,
  duplicateNDSymbolOnRoot,
  duplicateLeafNode,
  duplicatePrefix,
  duplicateSuffix,

  duplicateNDSymbolMutation,
  duplicateNodeMutation,
  duplicateNDSymbolOnRootMutation,
  duplicateLeafNodeMutation,
) where

import Control.Monad (guard)
import Data.Foldable.Extra (notNull)
import Data.List.Extra (allSame, anySame, transpose)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

import BAC.Base
import BAC.Fundamental.Mutation
import Utils.Utils ((.>), (|>))
import Control.Arrow (first)
import Data.Foldable (traverse_)

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

-- | Duplicate a nondecomposable symbol in a node (duplicate a non-terminal
--   nondecomposable morphism).
duplicateNDSymbol :: (Symbol, Symbol) -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbol (src, tgt) syms node = do
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

  let res0 = fromEdges do
        edge <- edges src_node
        if symbol edge /= tgt
        then return edge
        else do
          sym <- syms
          let dup_dict = dict edge |> Map.insert base sym
          return $ edge {dict = dup_dict}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> do
      let sym' = Map.lookup tgt (dict edge) |> fromJust
      sym <- syms
      let splitted_dict = dict edge |> Map.delete tgt |> Map.insert sym sym'
      return edge {dict = splitted_dict, target = res0}

duplicateNDSymbolMutation :: (Symbol, Symbol) -> [Symbol] -> BAC -> [Mutation]
duplicateNDSymbolMutation (src, tgt) syms node =
  [Duplicate (src, tgt) (fmap (src,) syms)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Duplicate (tgt, s) (fmap (,s) syms)

{- |
Duplicate a node (duplicate an object).

Examples:

>>> printBAC $ fromJust $ duplicateNode 3 (makeSplitter crescent [0,1]) crescent
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
duplicateNode :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateNode tgt splitter node = do
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
      let splitted_syms = splitter (symbol curr, symbol edge)
      sym <- splitted_syms
      let splitted_dict = dict edge |> Map.insert base sym
      return edge {dict = splitted_dict}

duplicateNodeMutation :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> [Mutation]
duplicateNodeMutation tgt splitter node = incoming_mutation ++ outgoing_mutation
  where
  incoming_mutation =
    suffix node tgt
    |> fmap symbol2
    |> fmap \(s1, s2) ->
      splitter (s1, s2)
      |> fmap (s1,)
      |> Duplicate (s1, s2)
  outgoing_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      splitter (tgt, s)
      |> fmap (,s)
      |> Duplicate (tgt, s)


-- | Duplicate a nondecomposable symbol in the root node (duplicate an initial
--   nondecomposable morphism).
duplicateNDSymbolOnRoot :: Symbol -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbolOnRoot tgt = duplicateNDSymbol (base, tgt)

duplicateNDSymbolOnRootMutation :: Symbol -> [Symbol] -> BAC -> [Mutation]
duplicateNDSymbolOnRootMutation tgt = duplicateNDSymbolMutation (base, tgt)

-- | Duplicate a leaf node (duplicate a nondecomposable terminal morphism).
duplicateLeafNode :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateLeafNode tgt splitter node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null
  duplicateNode tgt splitter node

duplicateLeafNodeMutation :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> [Mutation]
duplicateLeafNodeMutation = duplicateNodeMutation


duplicatePrefix :: (Symbol, Symbol) -> (Symbol -> [Symbol]) -> BAC -> Maybe BAC
duplicatePrefix (src, tgt) splitter node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let dup_list = arrowsUnder src_node tgt |> fmap symbol |> filter (/= base) |> (tgt :)

  let len = splitter tgt |> length
  guard $ len /= 0
  guard $ dup_list |> fmap splitter |> fmap length |> all (== len)
  guard $
    symbols src_node
    |> concatMap (\sym -> if sym `elem` dup_list then splitter sym else [sym])
    |> anySame
    |> not

  let res0 = fromEdges do
        edge <- edges (target src_arr)
        if symbol edge `notElem` dup_list
        then return edge
        else
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
          |> fmap \dict' -> edge {dict = dict'}

  fromReachable res0 $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner res -> return edge {target = res}
      AtBoundary ->
        dict edge
        |> Map.toList
        |> fmap (first \sym -> if sym `elem` dup_list then splitter sym else [sym])
        |> concatMap (\(syms, sym') -> syms |> fmap (,sym'))
        |> Map.fromList
        |> \dict' -> return edge {dict = dict', target = res0}

duplicateSuffix :: (Symbol, Symbol) -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateSuffix (src, tgt) splitter node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let len = splitter (src, tgt) |> length

  guard $ len /= 0

  arrowsUnder src_node tgt |> traverse_ \arr -> do
    let dup_list = arr `divide` tgt_subarr |> fmap symbol
      
    guard $
      dup_list
      |> fmap (symbol arr,)
      |> fmap splitter
      |> fmap length
      |> all (== len)
    guard $
      target arr
      |> symbols
      |> concatMap (\sym -> if sym `elem` dup_list then splitter (symbol arr, sym) else [sym])
      |> anySame
      |> not

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
        AtBoundary | is_outside -> return edge
        AtBoundary -> do
          sym <- splitter (symbol curr, symbol edge)
          let dict' = dict edge |> Map.insert base sym
          return edge {dict = dict'}
        AtInner res | null (src_arr `divide` (curr `join` edge)) ->
          return edge {target = res}
        AtInner res | is_outside ->
          dict edge
          |> Map.toList
          |> fmap (first \s -> if s `elem` dup_list' then splitter (sym', s) else [s])
          |> concatMap (\(s, r) -> s |> fmap (,r))
          |> Map.fromList
          |> \dict' -> return edge {dict = dict', target = res}
        AtInner res ->
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if s `elem` dup_list'
            then splitter (sym', s) `zip` splitter (sym, r)
            else [(s, r)]
          )
          |> Map.fromList
          |> \dict' -> return edge {dict = dict', target = res}
