{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Restructure (
  addEdge,
  removeEdge,
  alterEdges,
  relabel,
  alterSymbol,
  makeShifter,
) where

import Control.Monad (guard)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Tuple.Extra (dupe)
import Numeric.Natural (Natural)

import BAC.Base
import Utils.Utils ((|>))

-- $setup
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
Add an edge to the first position.  The categorical structure should not change after this
process.

Examples:

>>> printBAC $ fromJust $ cone |> addEdge (3,2) ()
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->2
    *0
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
-}
addEdge ::
  Monoid e
  => (Symbol, Symbol)
  -- ^ The pair of symbols of added edge.
  -> e
  -- ^ The carried value of edge to add.
  -> BAC e
  -> Maybe (BAC e)
addEdge (src, tgt) e node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)

  -- add edge to src node
  let src_node' =
        target src_arr
        |> edges
        |> (tgt_subarr {value = e} :)
        |> BAC

  -- rebuild BAC with the new node
  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {target = src_node'}

{- |
Remove the first occurance of an edge.  The categorical structure should not change after
this process.

Examples:

>>> cone' = fromJust $ cone |> addEdge (3,2) ()
>>> printBAC $ fromJust $ cone' |> removeEdge (3,2) ()
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
-}
removeEdge ::
  (Monoid e, Eq e)
  => (Symbol, Symbol)
  -- ^ The pair of symbols of removed edge.
  -> e
  -- ^ The carried value of edge to remove.
  -> BAC e
  -> Maybe (BAC e)
removeEdge (src, tgt) e node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)

  -- ensure that it can be removed
  let is_nd = nondecomposable (target src_arr) tgt
  let num = target src_arr |> edges |> filter (\edge -> symbol edge == tgt) |> length
  guard $ not is_nd || num > 1

  -- remove edge from src node
  let src_node' =
        target src_arr
        |> edges
        |> deleteIf (\edge -> symbol edge == tgt && value edge == e)
        |> BAC

  -- rebuild BAC with the new node
  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {target = src_node'}
  where
  deleteIf _ [] = []
  deleteIf f (h:t) = if f h then t else deleteIf f t

{- |
Collect and alter edges with specified symbols.  The categorical structure should not
change after this process.
-}
alterEdges ::
  (Monoid e, Eq e)
  => (Symbol, Symbol)
  -- ^ The pair of symbols of altered edges.
  -> (NonEmpty e -> NonEmpty e)
  -- ^ The function on carried values of edges to alter.
  -> BAC e
  -> Maybe (BAC e)
alterEdges (src, tgt) action node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)

  -- alter edges from src node
  let edges_to_alter = target src_arr |> edges |> filter (\edge -> symbol edge == tgt)
  let altered_edges =
        edges_to_alter
        |> NonEmpty.nonEmpty
        |> fmap (fmap value)
        |> fmap action
        |> fmap (fmap \e -> (head edges_to_alter) {value = e})
        |> maybe [] NonEmpty.toList
  let src_node' =
        target src_arr
        |> edges
        |> filter (\edge -> symbol edge /= tgt)
        |> (altered_edges ++)
        |> BAC

  -- rebuild BAC with the new node
  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {target = src_node'}

{- |
Relabel symbols in a given node.  The categorical structure should not change after this
process.

Examples:

>>> let remap = fromList [(0,0), (1,4), (2,1), (3,2), (4,3)] :: Dict
>>> printBAC $ fromJust $ relabel 3 remap cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2; 2->6; 3->4; 4->4
  - 0->4; 1->1; 2->2
    &1
    - 0->1
      *0
    - 0->2
  - 0->3; 1->1; 2->2
    *1

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2)]) cone
Nothing

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2), (4,4)]) cone
Nothing

>>> relabel 3 (fromList [(0,3), (1,4), (2,1), (3,2), (4,0)]) cone
Nothing
-}
relabel ::
  Monoid e
  => Symbol
  -- ^ The symbol referencing the node to relabel.
  -> Dict
  -- ^ The dictionary to relabel the symbols of the node.
  -> BAC e
  -> Maybe (BAC e)
relabel tgt mapping node = do
  tgt_node <- arrow node tgt |> fmap target

  -- validate the relabel mapping
  guard $ Map.lookup base mapping == Just base
  guard $ Map.keys mapping == symbols tgt_node
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  -- relabel symbols of the node `tgt_node`
  let tgt_node' = BAC do
        edge <- edges tgt_node
        return edge {dict = mapping `cat` dict edge}

  -- rebuild BAC with the new node
  fromReachable tgt_node' $ root node |> modifyUnder tgt \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {dict = dict edge `cat` unmapping, target = tgt_node'}

{- |
Alter a symbol in a node.  The categorical structure should not change after this process.

Examples:

>>> printBAC $ fromJust $ alterSymbol (3,1) 5 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6; 4->4; 5->4
  - 0->5; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
-}
alterSymbol ::
  Monoid e
  => (Symbol, Symbol)
  -- ^ The pair of symbols to be altered.
  -> Symbol
  -- ^ The new symbol.
  -> BAC e
  -> Maybe (BAC e)
alterSymbol (src, tgt) sym node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)

  -- construct the relabel mapping
  let mapping = symbols (target src_arr) |> fmap dupe |> Map.fromList |> Map.insert tgt sym
  node |> relabel src mapping

-- | Shift a symbol `tgt` on a node referenced by `src`, where `tgt` cannot be `base`.
--   It is typically used to modify symbols on multiple nodes, which is required when
--   calling `BAC.Fundamental.addLeafNode`, `BAC.Fundamental.addParentNode`,
--   `BAC.Fundamental.duplicateNode` and `BAC.Fundamental.splitNode`.
makeShifter :: Monoid e => BAC e -> Natural -> (Symbol, Symbol) -> Symbol
makeShifter node offset (src, tgt) =
  arrow node src |> fromJust |> target |> symbols |> maximum |> (* offset) |> (+ tgt)
