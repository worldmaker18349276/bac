{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module BAC.Fundamental.Remove (
  removeNDSymbol,
  removeNDSymbolOnRoot,
  removeNode,
  removeLeafNode,
  -- removePrefix,
  -- removeSuffix,
) where

import Control.Monad (guard)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map

import BAC.Base
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import Data.Maybe (fromJust)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Remove a nondecomposable symbol on a node, where the first parameter @(src, tgt) ::
(Symbol, Symbol)@ indicates the node to operate and the symbol on this node to remove.  In
categorical perspectives, it removes a non-terminal nondecomposable morphism, where
@(src, tgt)@ indicates the morphism to remove.

Identity morphism or decomposable morphism cannot be remove.  The decomposability of a
morphism can be checked by the function `nondecomposable`.  For simplicity, alternative
edges will always be constructed by joining edges adjacent to the edge to be removed,
which does not change the categorical properties.

Examples:

>>> printBAC $ cone |> removeNDSymbol (1,1) |> fromJust
- 0->1
- 0->2
  &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1

>>> printBAC $ cone |> removeNDSymbol (0,3) |> fromJust
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2

>>> printBAC $ cone |> removeNDSymbol (3,1) |> fromJust |> removeNDSymbol (3,4) |> fromJust
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3
    &1
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
    *1
-}
removeNDSymbol ::
  (Symbol, Symbol)
  -- ^ The pair of symbols indicating the morphism to be removed.
  -> BAC
  -> Maybe BAC
removeNDSymbol (src, tgt) node = do
  -- ensure that `(src, tgt)` is reachable and nondecomposable
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  guard $ nondecomposable src_node tgt

  -- remove edge of `tgt` from `src_node`
  let src_node' = fromEdges do
        edge <- edges src_node
        if symbol edge /= tgt
        then return edge
        else do
          -- add edges by joining the removed edge to outgoing edges
          subedge <- target tgt_subarr |> edges
          return $ tgt_subarr `join` subedge

  -- rebuild the whole tree
  fromReachable src_node' $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary ->
      [
        -- remove link from the removed symbol
        edge {dict = filtered_dict, target = src_node'},
        -- add an edge by joining incoming edge to the removed edge
        edge `join` tgt_subarr
      ]
      where
      filtered_dict = dict edge |> Map.delete tgt

-- | Remove a nondecomposable symbol on the root node (remove a nondecomposable initial
--   morphism).  See `removeNDSymbol` for details.
removeNDSymbolOnRoot :: Symbol -> BAC -> Maybe BAC
removeNDSymbolOnRoot tgt = removeNDSymbol (base, tgt)


{- |
Remove a node, where the first parameter @tgt :: Symbol@ indicates the node to remove.  In
categorical perspectives, it removes initial and terminal morphisms of an object
simultaneously, where `tgt` indicates the object to remove.

Root node cannot be removed.  For simplicity, alternative edges will always be constructed
by joining edges adjacent to the node to be removed, which does not change the categorical
properties.

Examples:

>>> printBAC $ fromJust $ removeNode 3 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2

>>> printBAC $ fromJust $ removeNode 4 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3

>>> printBAC $ fromJust $ removeNode 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0
-}
removeNode :: Symbol -> BAC -> Maybe BAC
removeNode tgt node = do
  -- ensure that `tgt` reference a proper subnode.
  guard $ locate (root node) tgt == Inner

  -- remove the node of `tgt`
  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    -- repace the incoming edge by joining this edge and outgoing edges
    AtBoundary -> do
      subedge <- target edge |> edges
      return $ edge `join` subedge
    -- remove symbols referencing the removed node
    AtInner subnode -> return edge {dict = filtered_dict, target = subnode}
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

-- | Remove a leaf node (remove a nondecomposable terminal morphism).  See `removeNode`
--   for details.
removeLeafNode :: Symbol -> BAC -> Maybe BAC
removeLeafNode tgt node = do
  tgt_node <- arrow node tgt |> fmap target
  guard $ tgt_node |> edges |> null

  removeNode tgt node


{- |
Remove a non-terminal decomposable morphism and all prefix morphisms, where the first
parameter @(src, tgt) :: (Symbol, Symbol)@ indicates the morphism to remove.

Identity morphism cannot be remove.
-}
removePrefix :: (Symbol, Symbol) -> BAC -> Maybe BAC
removePrefix (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)

  let src_node = target src_arr
  let remove_list = arrowsUnder src_node tgt |> fmap symbol |> filter (/= base) |> (tgt :)

  let src_node' =
        src_node
        |> edges
        |> filter (dict .> notElem tgt)
        |> fromEdges
  let syms0 = symbols src_node'
  guard $ symbols src_node |> filter (`notElem` remove_list) |> (== syms0)

  fromReachable src_node' $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner subnode -> return edge {target = subnode}
      AtBoundary -> return edge {dict = dict', target = src_node'}
        where
        dict' = dict edge |> Map.filterWithKey \s _ -> s `elem` syms0

{- |
Remove a non-terminal decomposable morphism and all suffix morphisms, where the first
parameter @(src, tgt) :: (Symbol, Symbol)@ indicates the morphism to remove.

Identity morphism cannot be remove.
-}
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
              AtInner subnode | null (src_arr `divide` (curr `join` edge)) ->
                return edge {target = subnode}
              AtInner subnode | null (src_arr `divide` (curr `join` edge)) ->
                return edge {target = subnode}
              AtInner subnode -> return edge {dict = dict', target = subnode}
                where
                dict' = target edge |> symbols |> foldr Map.delete (dict edge)

      guard $ symbols (target curr) |> filter (`notElem` remove_list) |> (== symbols res)

      return res

  fromReachable tgt_node lres
