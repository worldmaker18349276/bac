{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module BAC.Fundamental.Restructure (
  rewire,
  addEdge,
  removeEdge,
  relabel,
  relabelOnRoot,
  alterSymbol,

  addEdgeMutation,
  removeEdgeMutation,
  relabelMutation,
  relabelOnRootMutation,
  alterSymbolMutation,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (bimap))
import Data.List.Extra (snoc)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Tuple.Extra (both, dupe)

import BAC.Base
import BAC.Fundamental.Mutation
import Utils.Utils ((|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)

{- |
Rewire edges of a given node.

Examples:

>>> printBAC $ fromJust $ rewire 0 [1, 4, 3] cone
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

>>> printBAC $ fromJust $ rewire 3 [1, 4, 3] cone
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

>>> rewire 3 [1, 5, 3] cone
Nothing
-}
rewire ::
  Symbol         -- ^ The symbol referencing to the node to rewire.
  -> [Symbol]    -- ^ The list of pairs of symbols of rewired edges.
  -> BAC
  -> Maybe BAC
rewire src tgts node = do
  src_arr <- arrow node src
  let nd_syms = target src_arr |> edgesND |> fmap symbol
  src_edges' <- tgts |> traverse (arrow (target src_arr))
  let res0 = fromEdges src_edges'

  let nd_syms' = res0 |> edgesND |> fmap symbol
  guard $ nd_syms == nd_syms'

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {target = res0}

{- | Add an edge.  The categorical structure should not change after adding this edge.

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
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let new_syms =
        src_arr
        |> target
        |> edges
        |> fmap symbol
        |> (`snoc` tgt)
  node |> rewire src new_syms

addEdgeMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
addEdgeMutation (src, tgt) _node = [Insert (src, tgt)]

{- | Remove an edge.  The categorical structure should not change after removing this edge.

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
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let new_syms =
        src_arr
        |> target
        |> edges
        |> fmap symbol
        |> filter (/= tgt)
  node |> rewire src new_syms

removeEdgeMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
removeEdgeMutation (src, tgt) _node = [Delete (src, tgt)]

{- |
Relabel symbols in a given node.

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
  tgt_arr <- arrow node tgt
  guard $ base `Map.member` mapping && mapping ! base == base
  guard $ Map.keys mapping == symbols (target tgt_arr)
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  let res0 = fromEdges do
        edge <- edges (target tgt_arr)
        return edge {dict = mapping `cat` dict edge}
  fromReachable res0 $ node |> modifyUnder tgt \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict edge `cat` unmapping, target = res0}

relabelMutation :: Symbol -> Dict -> BAC -> [Mutation]
relabelMutation tgt mapping node =
  arrow node tgt
  |> fromJust
  |> target
  |> edges
  |> fmap symbol
  |> fmap (id &&& (mapping !))
  |> fmap (both (tgt,))
  |> unzip
  |> uncurry Transfer
  |> (: [])
  |> if tgt == base then (++ root_mutation) else id
  where
  root_mutation =
    mapping
    |> Map.toList
    |> concatMap \(sym, sym') ->
      arrow node sym
      |> fromJust
      |> target
      |> edges
      |> fmap symbol
      |> fmap dupe
      |> fmap ((sym,) `bimap` (sym',))
      |> unzip
      |> uncurry Transfer
      |> (: [])

-- | Relabel symbols in the root node.
relabelOnRoot :: Dict -> BAC -> Maybe BAC
relabelOnRoot = relabel base

relabelOnRootMutation :: Dict -> BAC -> [Mutation]
relabelOnRootMutation = relabelMutation base

{- |
Alter a symbol in a node.

Examples:

>>> printBAC $ fromJust $ alterSymbol (3, 1) 5 cone
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
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let syms = src_arr |> target |> symbols
  guard $ syms |> filter (/= tgt) |> notElem sym
  let mapping = syms |> fmap dupe |> Map.fromList |> Map.insert tgt sym
  node |> relabel src mapping

alterSymbolMutation :: (Symbol, Symbol) -> Symbol -> BAC -> [Mutation]
alterSymbolMutation (src, tgt) sym node =
  [Transfer [(src, tgt)] [(src, sym)] | is_edge]
  |> if src == base then (++ root_mutation) else id
  where
  is_edge =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> elem tgt
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap dupe
    |> fmap ((tgt,) `bimap` (sym,))
    |> unzip
    |> uncurry Transfer
    |> (: [])
