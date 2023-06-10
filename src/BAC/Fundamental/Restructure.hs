{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module BAC.Fundamental.Restructure (
  rewire,
  addEdge,
  removeEdge,
  relabel,
  alterSymbol,
  makeShifter,
) where

import Control.Monad (guard)
import Data.List.Extra (snoc)
import qualified Data.Map.Strict as Map
import Data.Tuple (swap)
import Data.Tuple.Extra (dupe)
import Numeric.Natural (Natural)

import BAC.Base
import Utils.Utils ((|>))
import Data.Maybe (fromJust)

-- $setup
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
Rewire edges of a given node.  The categorical structure should not change after this
process.

Examples:

>>> printBAC $ fromJust $ rewire (0, [1,4,3]) cone
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
- 0->4; 1->2; 2->6
  *1

>>> printBAC $ fromJust $ rewire (3, [1,4,3]) cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
      &2
  - 0->3
    *2
  - 0->4; 1->2; 2->3
    *1

>>> rewire (3, [1,5,3]) cone
Nothing
-}
rewire ::
  (Symbol, [Symbol])  -- ^ The list of pairs of symbols of rewired edges.
  -> BAC
  -> Maybe BAC
rewire (src, tgts) node = do
  -- find the node referenced by the symbol `src`
  src_node <- arrow node src |> fmap target
  -- construct new node with edges referenced by symbols `tgts`
  src_edges' <- tgts |> traverse (arrow src_node)
  let src_node' = fromEdges src_edges'

  -- ensure that symbol list of this node doesn't change after rewiring
  guard $ symbols src_node == symbols src_node'

  -- rebuild BAC with the new node
  fromReachable src_node' $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {target = src_node'}

{- |
Add an edge.  The categorical structure should not change after this process.

Examples:

>>> printBAC $ fromJust $ cone |> addEdge (3,2)
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->2
    *0
  - 0->4; 1->2; 2->3
    *1
-}
addEdge ::
  (Symbol, Symbol)  -- ^ The pair of symbols of added edge.
  -> BAC
  -> Maybe BAC
addEdge (src, tgt) node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  -- construct symbol list for rewiring
  let syms = src_arr |> target |> edges |> fmap symbol
  let syms' = syms `snoc` tgt
  node |> rewire (src, syms')

{- |
Remove an edge.  The categorical structure should not change after this process.

Examples:

>>> cone' = fromJust $ cone |> addEdge (3,2)
>>> printBAC $ fromJust $ cone' |> removeEdge (3,2)
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
  (Symbol, Symbol)  -- ^ The pair of symbols of removed edge.
  -> BAC
  -> Maybe BAC
removeEdge (src, tgt) node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  -- construct symbol list for rewiring
  let syms = src_arr |> target |> edges |> fmap symbol
  let syms' = syms |> filter (/= tgt)
  node |> rewire (src, syms')

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
  - 0->3; 1->1; 2->2
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->1; 2->2
    *1

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2)]) cone
Nothing

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2), (4,4)]) cone
Nothing

>>> relabel 3 (fromList [(0,3), (1,4), (2,1), (3,2), (4,0)]) cone
Nothing
-}
relabel ::
  Symbol    -- ^ The symbol referencing to the node to relabel.
  -> Dict   -- ^ The dictionary to relabel the symbols of the node.
  -> BAC
  -> Maybe BAC
relabel tgt mapping node = do
  tgt_node <- arrow node tgt |> fmap target

  -- validate the relabeling mapping
  guard $ Map.lookup base mapping == Just base
  guard $ Map.keys mapping == symbols tgt_node
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  -- relabel symbols of the node `tgt_node`
  let tgt_node' = fromEdges do
        edge <- edges tgt_node
        return edge {dict = mapping `cat` dict edge}

  -- rebuild BAC with the new node
  fromReachable tgt_node' $ node |> modifyUnder tgt \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict edge `cat` unmapping, target = tgt_node'}

{- |
Alter a symbol in a node.  The categorical structure should not change after this process.

Examples:

>>> printBAC $ fromJust $ alterSymbol (3,1) 5 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6; 4->4; 5->4
  - 0->4; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->5; 1->2; 2->3
    *1
-}
alterSymbol ::
  (Symbol, Symbol)  -- ^ The pair of symbols to be altered.
  -> Symbol         -- ^ The new symbol.
  -> BAC
  -> Maybe BAC
alterSymbol (src, tgt) sym node = do
  -- ensure that `(src, tgt)` is reachable
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)

  -- ensure that it is valid to alter the symbol `tgt` to `sym` on the node of `src`.
  let syms = src_arr |> target |> symbols
  guard $ syms |> filter (/= tgt) |> notElem sym

  -- construct the relabeling mapping
  let mapping = syms |> fmap dupe |> Map.fromList |> Map.insert tgt sym
  node |> relabel src mapping

-- | Shift a symbol `tgt` on a node referenced by `src`, where `tgt` cannot be `base`.
--   It is typically used to modify symbols on multiple nodes, which is required when
--   calling `BAC.Fundamental.addLeafNode`, `BAC.Fundamental.addParantNode`,
--   `BAC.Fundamental.duplicateNode` and `BAC.Fundamental.splitNode`.
makeShifter :: BAC -> Natural -> (Symbol, Symbol) -> Symbol
makeShifter node offset (src, tgt) =
  arrow node src |> fromJust |> target |> symbols |> maximum |> (* offset) |> (+ tgt)
