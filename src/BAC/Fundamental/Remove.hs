{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module BAC.Fundamental.Remove (
  relativeNondecomposablesOutgoing,
  relativeNondecomposablesIncoming,
  removeNDSymbol,
  removeNDSymbolOnRoot,
  relativeNondecomposables',
  removeNode,
  removeLeafNode,
) where

import Control.Arrow (first, (&&&))
import Control.Monad (guard)
import Data.List.Extra (groupOn, nubSort, nubSortOn)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, maybeToList)

import BAC.Base
import Utils.Utils ((|>), (.>))

-- $setup
-- >>> import Data.Maybe (fromJust)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Find all morphism-relative nondecomposable morphisms which are outgoing morphism of the
source of such morphism, where the second parameter @(src, tgt) :: (Symbol, Symbol)@
indicates the relative morphism.
Morphism-relative nondecomposable morphism can only be decomposed into non-trivial 2-chain
containing the relative morphism, and will become nondecomposable after removing it.

Examples:

>>> relativeNondecomposablesOutgoing cone (1,1)
[]
>>> relativeNondecomposablesOutgoing cone (0,3)
[(0,4)]
>>> relativeNondecomposablesOutgoing cone (3,1)
[]
>>> relativeNondecomposablesOutgoing (cone |> removeNDSymbol (3,1) |> fromJust) (3,4)
[(3,2),(3,3)]
-}
relativeNondecomposablesOutgoing :: Monoid e => BAC e -> (Symbol, Symbol) -> [(Symbol, Symbol)]
relativeNondecomposablesOutgoing node (src_sym, tgt_sym) = do
  (src_arr, tgt_subarr) <- arrow2 node (src_sym, tgt_sym) |> maybeToList
  guard $ nondecomposable (target src_arr) tgt_sym

  let remaining =
        target src_arr
        |> edgesND
        |> filter (symbol .> (/= tgt_sym))
        |> concatMap (dict .> Map.elems)
  let alt_syms =
        target tgt_subarr
        |> edgesND
        |> fmap (symbol .> (dict tgt_subarr !))
  alt_sym <- alt_syms |> filter (`notElem` remaining) |> nubSort
  return (src_sym, alt_sym)

{- |
Find all morphism-relative nondecomposable morphisms which are incoming morphism of the
target of such morphism, where the second parameter @(src, tgt) :: (Symbol, Symbol)@
indicates the relative morphism.

Examples:

>>> relativeNondecomposablesIncoming cone (1,1)
[]
>>> relativeNondecomposablesIncoming cone (0,3)
[]
>>> relativeNondecomposablesIncoming cone (3,1)
[]
>>> relativeNondecomposablesIncoming (cone |> removeNDSymbol (3,1) |> fromJust) (3,4)
[(0,4)]
-}
relativeNondecomposablesIncoming :: Monoid e => BAC e -> (Symbol, Symbol) -> [(Symbol, Symbol)]
relativeNondecomposablesIncoming node (src_sym, tgt_sym) = do
  (src_arr, _tgt_subarr) <- arrow2 node (src_sym, tgt_sym) |> maybeToList
  guard $ nondecomposable (target src_arr) tgt_sym

  (arr, syms') <-
    suffixND node src_sym
    |> nubSortOn symbol2
    |> groupOn (symbol2 .> fst)
    |> fmap (head .> fst &&& fmap (snd .> symbol))
  let remaining =
        target arr
        |> edgesND
        |> fmap (\edge -> if symbol edge `elem` syms' then edge |> dict |> Map.delete tgt_sym else edge |> dict)
        |> concatMap Map.elems
  alt_sym <-
    target arr
    |> symbols
    |> filter (/= base)
    |> filter (`notElem` remaining)
  return (symbol arr, alt_sym)

{- |
Remove a nondecomposable symbol on a node, where the first parameter @(src, tgt) ::
(Symbol, Symbol)@ indicates the node to operate and the symbol on this node to remove.  In
categorical perspectives, it removes a non-terminal nondecomposable morphism, where
@(src, tgt)@ indicates the morphism to remove.

Identity morphism or decomposable morphism cannot be remove.  The decomposability of a
morphism can be checked by the function `nondecomposable`.  The direct edges for relative
morphisms should be added before removing, which can be determined by
`relativeNondecomposablesOutgoing` and `relativeNondecomposablesIncoming`.

Examples:

>>> printBAC $ cone |> removeNDSymbol (1,1) |> fromJust
[1;]
[3;4;2;6;4;]
  [1;2;3;]
    &0
    [1;]
    [2;]
  [4;2;3;]
    *0

>>> printBAC $ cone |> addEdge (0,4) () |> fromJust |> removeNDSymbol (0,3) |> fromJust
[4;2;6;]
  [1;]
    &0
  [2;]
[1;2;]
  [1;]
    *0

>>> printBAC $ cone |> removeNDSymbol (3,1) |> fromJust |> addEdge (3,2) () |> fromJust |> addEdge (3,3) () |> fromJust |> addEdge (0,4) () |> fromJust |> removeNDSymbol (3,4) |> fromJust
[4;2;6;]
  [1;]
    &0
  [2;]
    &1
[1;2;]
  [1;]
    *0
[3;2;6;]
  [3;]
    *1
  [2;]
    *0
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

  -- check outgoing alternative paths
  guard $
    relativeNondecomposablesOutgoing node (src, tgt)
    |> fmap snd
    |> all \sym -> src_node |> edges |> fmap symbol |> elem sym

  -- check incoming alternative paths
  guard $
    relativeNondecomposablesIncoming node (src, tgt)
    |> fmap (first (arrow node .> fromJust .> target))
    |> all \(node', sym) -> node' |> edges |> fmap symbol |> elem sym

  -- remove edge of `tgt` from `src_node`
  let src_node' = src_node |> edges |> filter (symbol .> (/= tgt)) |> BAC

  -- rebuild the whole tree
  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {dict = filtered_dict, target = src_node'}
      where
      -- remove link from the removed symbol
      filtered_dict = dict edge |> Map.delete tgt

-- | Remove a nondecomposable symbol on the root node (remove a nondecomposable initial
--   morphism).  See `removeNDSymbol` for details.
removeNDSymbolOnRoot :: Monoid e => Symbol -> BAC e -> Maybe (BAC e)
removeNDSymbolOnRoot tgt = removeNDSymbol (base, tgt)


{- |
Find all object-relative nondecomposable morphisms, where the second parameter @src ::
Symbol@ indicates the relative object.
Object-relative nondecomposable morphism can only be decomposed into non-trivial 2-chain
containing the relative object, and will become nondecomposable after removing it.

Examples:

>>> relativeNondecomposables' cone 3
[(0,4)]
>>> relativeNondecomposables' cone 4
[(3,2),(3,3)]
>>> relativeNondecomposables' cone 2
[]
-}
relativeNondecomposables' :: Monoid e => BAC e -> Symbol -> [(Symbol, Symbol)]
relativeNondecomposables' node src_sym = do
  (arr, syms') <-
    suffixND node src_sym
    |> nubSortOn symbol2
    |> groupOn (symbol2 .> fst)
    |> fmap (head .> fst &&& fmap (snd .> symbol))
  let remaining =
        target arr
        |> edgesND
        |> filter (symbol .> (`notElem` syms'))
        |> concatMap (dict .> Map.elems)
  let alt_syms =
        target arr
        |> symbols
        |> filter (/= base)
        |> filter (`notElem` syms')
        |> filter (`notElem` remaining)
  let decomposables =
        alt_syms
        |> fmap (arrow (target arr) .> fromJust)
        |> concatMap (dict .> Map.delete base .> Map.elems)
  alt_sym <- alt_syms |> filter (`notElem` decomposables)
  return (symbol arr, alt_sym)

{- |
Remove a node, where the first parameter @tgt :: Symbol@ indicates the node to remove.  In
categorical perspectives, it removes initial and terminal morphisms of an object
simultaneously, where `tgt` indicates the object to remove.

Root node cannot be removed.  The direct edges for relative morphisms should be added
before removing, which can be determined by 'relativeNondecomposables''.

Examples:

>>> printBAC $ cone |> addEdge (0,4) () |> fromJust |> removeNode 3 |> fromJust
[4;2;6;]
  [1;]
    &0
  [2;]
[1;2;]
  [1;]
    *0

>>> printBAC $ cone |> addEdge (3,2) () |> fromJust |> addEdge (3,3) () |> fromJust |> removeNode 4 |> fromJust
[1;2;]
  [1;]
    &0
[3;2;6;]
  [3;]
  [2;]
    *0

>>> printBAC $ fromJust $ removeNode 2 cone
[1;]
[3;4;6;4;]
  [1;3;]
    &0
    [2;]
  [4;3;]
    *0
-}
removeNode :: Monoid e => Symbol -> BAC e -> Maybe (BAC e)
removeNode tgt node = do
  -- ensure that `tgt` reference a proper subnode.
  guard $ locate (root node) tgt == Inner

  -- check alternative paths
  guard $
    relativeNondecomposables' node tgt
    |> fmap (first (arrow node .> fromJust .> target))
    |> all \(node', sym) -> node' |> edges |> fmap symbol |> elem sym

  -- remove the node of `tgt`
  fromInner $ root node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtBoundary -> []
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
