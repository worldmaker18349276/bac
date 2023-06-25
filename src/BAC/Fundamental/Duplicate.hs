{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Duplicate (
  duplicateNDSymbol,
  duplicateNDSymbolOnRoot,
  duplicateNode,
  duplicateLeafNode,
  duplicatePrefix,
  duplicateSuffix,
) where

import Control.Arrow (first)
import Control.Monad (guard)
import Data.Foldable (traverse_)
import Data.Foldable.Extra (notNull)
import Data.List.Extra (anySame, transpose, replace)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map

import BAC.Base
import Utils.Utils ((|>))

-- $setup
-- >>> import Data.Maybe (fromJust)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Duplicate a nondecomposable symbol on a node, where `src` indicates the node to operate,
`tgt` indicates the symbol to duplicate, and `syms` is a list of symbols of duplication.
It is equivalent to split a nondecomposable symbol: @splitSymbol (src, tgt) (syms \`zip\`
repeat [])@.

In categorical perspectives, it duplicates a non-terminal nondecomposable morphism, where
@(src, tgt)@ indicates a nondecomposable morphism to duplicate, and @(src, sym)@ for all
@sym <- syms@ will indicate a duplicated morphism.

Examples:

>>> printBAC $ fromJust $ duplicateNDSymbol (3,1) [1,5] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
  - 0->5; 1->2; 2->3
    *1

>>> printBAC $ fromJust $ splitSymbol (3,1) [(1,[]),(5,[])] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
  - 0->5; 1->2; 2->3
    *1
-}
duplicateNDSymbol :: (Symbol, Symbol) -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbol (src, tgt) syms node = do
  guard $ notNull syms
  -- ensure that `(src, tgt)` is reachable, proper and nondecomposable
  src_arr <- arrow node src
  let src_node = target src_arr
  guard $ locate (root src_node) tgt == Inner
  guard $ nondecomposable src_node tgt
  -- ensure that it is valid to relace `tgt` with `syms`
  guard $ src_node |> symbols |> replace [tgt] syms |> anySame |> not

  let src_node' = fromEdges do
        edge <- edges src_node
        if symbol edge /= tgt
        then return edge
        else do
          -- duplicate the edge of `(src, tgt)` by replacing link `(base, tgt)` with `(base, sym)`
          sym <- syms
          let dup_dict = dict edge |> Map.insert base sym
          return $ edge {dict = dup_dict}

  fromReachable src_node' $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> do
      -- replace link `(tgt, _)` with `(sym, _)` for `sym <- syms`
      let duplicate (s, r) = if s == tgt then [(s', r) | s' <- syms] else [(s, r)]
      let splitted_dict = dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
      return edge {dict = splitted_dict, target = src_node'}

-- | Duplicate a nondecomposable symbol on the root node (duplicate an initial
--   nondecomposable morphism).  See `duplicateNDSymbol` for details.
duplicateNDSymbolOnRoot :: Symbol -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbolOnRoot tgt = duplicateNDSymbol (base, tgt)


{- |
Duplicate a node, with parameters @tgt :: Symbol@, the symbol of the node to duplicate,
and @shifters :: [(Symbol, Symbol) -> Symbol]@, list of shifter functions.  Duplicating a
leaf node is equivalent to split a node: @splitNode tgt (shifters \`zip\` repeat [])@.

In categorical perspectives, it duplicates an object, where `tgt` indicates the object to
duplicate.  For all incoming morphisms of this object, say @(s1, s2)@, the pair of symbol
@(s1, shifter (s1, s2))@ for @shifter <- shifters@ will indicate the incoming morphism of
duplicated object with the same source object; for all outgoing morphism of this object,
say @(s1, s2)@, the pair of symbol @(shifter (base, s1), s2)@ for @shifter <- shifters@
will indicate the outgoing morphism of duplicated object with the same target object.

Examples:

>>> printBAC $ fromJust $ duplicateNode 4 (fmap (makeShifter cone) [0,1,2]) cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->10; 8->10; 9->16; 12->16
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
      &2
  - 0->4; 1->2; 2->3
    *1
  - 0->5; 1->2; 2->3
    &3
    - 0->1
      *0
    - 0->2
      *2
  - 0->8; 1->2; 2->3
    *3
  - 0->9; 1->2; 2->3
    &4
    - 0->1
      *0
    - 0->2
      *2
  - 0->12; 1->2; 2->3
    *4

>>> printBAC $ fromJust $ duplicateNode 3 (fmap (makeShifter crescent) [0,1]) crescent
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

>>> printBAC $ fromJust $ splitNode 3 (fmap (makeShifter crescent) [0,1] `zip` repeat []) crescent
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
duplicateNode :: Symbol -> [(Symbol, Symbol) -> Symbol] -> BAC -> Maybe BAC
duplicateNode tgt shifters node = do
  -- ensure that `tgt` is reachable and proper
  guard $ locate (root node) tgt |> (== Inner)
  let splitter = sequence shifters
  -- validate `splitter`
  guard $
    arrowsUnder node tgt
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> concatMap (\(s, r) -> if r == tgt then splitter (symbol arr, s) else [s])
      |> anySame
      |> not

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
      -- duplicate incoming edges of the node of `tgt`
      let splitted_syms = splitter (symbol curr, symbol edge)
      sym <- splitted_syms
      let splitted_dict = dict edge |> Map.insert base sym
      return edge {dict = splitted_dict}


-- | Duplicate a leaf node (duplicate a nondecomposable terminal morphism).  See
--   `duplicateNode` for details.
duplicateLeafNode :: Symbol -> [(Symbol, Symbol) -> Symbol] -> BAC -> Maybe BAC
duplicateLeafNode tgt shifters node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null
  duplicateNode tgt shifters node


duplicatePrefix :: (Symbol, Symbol) -> [Symbol -> Symbol] -> BAC -> Maybe BAC
duplicatePrefix (src, tgt) shifters node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let dup_list = arrowsUnder src_node tgt |> fmap symbol |> filter (/= base) |> (tgt :)

  let len = length shifters
  let splitter = sequence shifters
  guard $ len /= 0
  guard $
    symbols src_node
    |> concatMap (\sym -> if sym `elem` dup_list then splitter sym else [sym])
    |> anySame
    |> not

  let src_node' = fromEdges do
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

  fromReachable src_node' $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner subnode -> return edge {target = subnode}
      AtBoundary ->
        dict edge
        |> Map.toList
        |> fmap (first \sym -> if sym `elem` dup_list then splitter sym else [sym])
        |> concatMap (\(syms, sym') -> syms |> fmap (,sym'))
        |> Map.fromList
        |> \dict' -> return edge {dict = dict', target = src_node'}

duplicateSuffix :: (Symbol, Symbol) -> [(Symbol, Symbol) -> Symbol] -> BAC -> Maybe BAC
duplicateSuffix (src, tgt) shifters node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let len = length shifters
  let splitter = sequence shifters

  guard $ len /= 0

  arrowsUnder src_node tgt |> traverse_ \arr -> do
    let dup_list = arr `divide` tgt_subarr |> fmap symbol
      
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
        AtInner subnode | null (src_arr `divide` (curr `join` edge)) ->
          return edge {target = subnode}
        AtInner subnode | is_outside ->
          dict edge
          |> Map.toList
          |> fmap (first \s -> if s `elem` dup_list' then splitter (sym', s) else [s])
          |> concatMap (\(s, r) -> s |> fmap (,r))
          |> Map.fromList
          |> \dict' -> return edge {dict = dict', target = subnode}
        AtInner subnode ->
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if s `elem` dup_list'
            then splitter (sym', s) `zip` splitter (sym, r)
            else [(s, r)]
          )
          |> Map.fromList
          |> \dict' -> return edge {dict = dict', target = subnode}
