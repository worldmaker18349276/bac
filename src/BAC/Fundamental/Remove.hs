{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module BAC.Fundamental.Remove (
  removeNDSymbol,
  removeNDSymbolOnRoot,
  removeNode,
  removeLeafNode,
) where

import Control.Monad (guard)
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
  &1
  - 0->1
    *0
  - 0->2
- 0->4; 1->2; 2->6
  *1

>>> printBAC $ cone |> removeNDSymbol (3,1) |> fromJust |> removeNDSymbol (3,4) |> fromJust
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3
    &1
  - 0->2
    *0
  - 0->3
    *1
- 0->4; 1->2; 2->6
  &2
  - 0->1
    *0
  - 0->2
    *1
- 0->4; 1->2; 2->6
  *2
-}
removeNDSymbol ::
  Monoid e
  => (Symbol, Symbol)
  -- ^ The pair of symbols indicating the morphism to be removed.
  -> BAC e
  -> Maybe (BAC e)
removeNDSymbol (src, tgt) node = do
  -- ensure that `(src, tgt)` is reachable and nondecomposable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  guard $ nondecomposable src_node tgt

  -- remove edge of `tgt` from `src_node`
  let src_node' = BAC do
        edge <- edges src_node
        if symbol edge /= tgt
        then return edge
        else do
          -- add edges by joining the removed edges to outgoing edges
          subedge <- target edge |> edges
          return $ edge `join` subedge

  -- rebuild the whole tree
  let removed_edges = path src_node tgt
  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    -- add edges by joining incoming edge to the removed edges
    AtBoundary -> removed_edges |> fmap (join edge) |> (filtered_edge :)
      where
      -- remove link from the removed symbol
      filtered_dict = dict edge |> Map.delete tgt
      filtered_edge = edge {dict = filtered_dict, target = src_node'}

-- | Remove a nondecomposable symbol on the root node (remove a nondecomposable initial
--   morphism).  See `removeNDSymbol` for details.
removeNDSymbolOnRoot :: Monoid e => Symbol -> BAC e -> Maybe (BAC e)
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
  &1
  - 0->1
    *0
  - 0->2
- 0->4; 1->2; 2->6
  *1

>>> printBAC $ fromJust $ removeNode 4 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3
    &1
  - 0->2
    *0
  - 0->3
    *1

>>> printBAC $ fromJust $ removeNode 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0
-}
removeNode :: Monoid e => Symbol -> BAC e -> Maybe (BAC e)
removeNode tgt node = do
  -- ensure that `tgt` reference a proper subnode.
  guard $ locate (root node) tgt == Inner

  -- remove the node of `tgt`
  fromInner $ root node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    -- replace the incoming edge by joining this edge and outgoing edges
    AtBoundary -> target edge |> edges |> fmap (join edge)
    AtInner subnode -> return filtered_edge
      where
      -- remove symbols referencing the removed node
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)
      filtered_edge = edge {dict = filtered_dict, target = subnode}

-- | Remove a leaf node (remove a nondecomposable terminal morphism).  See `removeNode`
--   for details.
removeLeafNode :: Monoid e => Symbol -> BAC e -> Maybe (BAC e)
removeLeafNode tgt node = do
  tgt_node <- arrow node tgt |> fmap target
  guard $ tgt_node |> edges |> null

  removeNode tgt node
