{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

module BAC.Fundamental.Zip (
  eqStruct,
  zipArrows,
  canonicalizeRootNode,
  canonicalizeArrow,
  canonicalizeNode,
  forwardSymbolTrieUnder,
  backwardSymbolTrieUnder,
  zipSuffixes,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard, mzero)
import Data.Bifunctor (bimap, first, second)
import Data.List (sort, transpose, nub)
import Data.List.Extra (allSame, anySame, nubSortOn, nubOn)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Prelude hiding (compare, map)

import Utils.EqlistSet (canonicalizeGradedEqlistSet)
import Utils.Utils ((.>), (|>))
import BAC.Base

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)
-- >>> import Data.Map (elems)


-- | Structural equality, the equality of nodes up to rewiring.
--   Nodes should have the same symbol list, and equality of child nodes are not checked.
--   The node with the same structure can be unioned by merging their edges.
eqStruct :: [BAC] -> Bool
eqStruct = fmap edgesND .> fmap (fmap dict) .> allSame

{- |
Zip arrows of BACs, which shows the equality of nodes up to rewiring and relabelling.
Also, the equality of child nodes are not checked.  The correspondence between
nondecomposable edges of the root nodes should be provided.
-}
zipArrows :: [(BAC, [Symbol])] -> Maybe [[Arrow]]
zipArrows nodes_prefix = do
  -- check the given nondecomposable symbols
  guard $
    nodes_prefix
    |> fmap (edgesND .> fmap symbol .> sort `bimap` sort)
    |> all (uncurry (==))

  -- ensure that they can be zipped
  -- find dictionaries of nondecomposable edges to zip
  let dicts =
        nodes_prefix
        |> fmap \(node, nd_syms) ->
          nd_syms
          |> fmap (arrow node .> fromJust .> dict)
  -- relabel symbols according to the order of nondecomposable edges
  let maps =
        dicts
        |> fmap (concatMap Map.elems .> nub)
        |> fmap ((base :) .> (`zip` [base..]) .> Map.fromList)
  -- dictionaries should become the same after relabelling
  guard $ maps `zip` dicts |> fmap (sequence .> fmap (uncurry cat)) |> allSame

  -- zip all arrows
  let arrs =
        nodes_prefix
        |> fmap \(node, nd_syms) ->
          nd_syms
          |> fmap (arrow node .> fromJust)
          |> fmap ((id &&& (target .> arrows)) .> sequence .> fmap (uncurry join))
          |> concatMap (nubOn symbol .> (root node :))
  return $ arrs |> transpose

{- |
Find mappings to canonicalize the order of symbols of the root node.  It will return
multiple mappings if it possesses some symmetries.  The absolute order has no meaning, but
can be used to check the isomorphism between nodes.  The relative order between these
mappings forms automorphism of this BAC.

Examples:

>>> fmap elems $ canonicalizeRootNode crescent
[[0,1,2,3,4]]

>>> fmap elems $ canonicalizeRootNode $ target $ fromJust $ arrow crescent 1
[[0,1,2,3,4,5,6],[0,1,2,3,6,5,4],[0,3,2,1,4,5,6],[0,3,2,1,6,5,4],[0,4,5,6,1,2,3],[0,6,5,4,1,2,3],[0,4,5,6,3,2,1],[0,6,5,4,3,2,1]]
-}
canonicalizeRootNode :: BAC -> [Dict]
canonicalizeRootNode node =
  node
  |> edgesND
  |> fmap dict
  |> fmap Map.elems
  |> canonicalizeGradedEqlistSet (arrow node .> fromJust .> target)
  |> fmap (concat .> nub .> (base :))
  |> fmap ((`zip` [base..]) .> Map.fromList)

{- |
Find mappings to canonicalize the order of symbols of the target node of an arrow.  The
induced automorphisms are invariant under the mapping of the arrow.  It can be used to
check the upper isomorphism between objects.

Examples:

>>> fmap elems $ canonicalizeArrow $ fromJust $ arrow crescent 1
[[0,1,2,5,3,4,6],[0,3,4,6,1,2,5]]
-}
canonicalizeArrow :: Arrow -> [Dict]
canonicalizeArrow arr =
  target arr
  |> edgesND
  |> fmap dict
  |> fmap Map.elems
  |> canonicalizeGradedEqlistSet (dict arr !)
  |> fmap (concat .> nub .> (base :))
  |> fmap ((`zip` [base..]) .> Map.fromList)

{- |
Find mappings to canonicalize the order of symbols of a subnode specified by given symbol.
The induced automorphisms are invariant under the mapping of incoming edges.

Examples:

>>> fmap elems $ fromJust $ canonicalizeNode crescent 1
[[0,1,2,5,3,4,6],[0,3,4,6,1,2,5]]
-}
canonicalizeNode :: BAC -> Symbol -> Maybe [Dict]
canonicalizeNode node tgt = do
  guard $ tgt /= base
  tgt_arr <- arrow node tgt
  let keys =
        tgt
        |> suffixND node
        |> fmap (snd .> dict .> fmap (: []))
        |> foldl (Map.unionWith (++)) Map.empty
  return $
    target tgt_arr
    |> edgesND
    |> fmap dict
    |> fmap Map.elems
    |> canonicalizeGradedEqlistSet (keys !)
    |> fmap (concat .> nub .> (base :))
    |> fmap ((`zip` [base..]) .> Map.fromList)

{- |
Collect all maximum chains to a node into a trie.
It is a tree such that its paths correspond to maximum chains, which is represented as a
sequence of pairs of symbols, and each pair of symbols indicates a nondecomposable
morphism.  Just like BAC, the nodes of this trie is implicitly shared.

Examples:

>>> putStr $ showTree $ fromJust $ forwardSymbolTrieUnder 6 cone
{(0,3):{(3,1):{(4,2):{}},(3,4):{(4,2):{}}}}
-}
forwardSymbolTrieUnder :: Symbol -> BAC -> Maybe (Tree (Symbol, Symbol))
forwardSymbolTrieUnder sym = fromReachable res0 . foldUnder sym \curr results ->
  edges (target curr) `zip` results
  |> mapMaybe (second (fromReachable res0) .> sequence)
  |> fmap (first symbol)
  |> filter (fst .> nondecomposable (target curr))
  |> fmap (first (symbol curr,))
  |> Map.fromList
  |> Tree
  where
  res0 = Tree Map.empty

{- |
Collect all maximum chains to a node into a reversed trie.
It is a tree such that its paths correspond to the reverse of maximum chains, which is
represented as a sequence of pairs of symbols, and each pair of symbols indicates a
nondecomposable morphism.  Just like BAC, the nodes of this trie is implicitly shared.

Examples:

>>> putStr $ showTree $ fromJust $ backwardSymbolTrieUnder 6 cone
{(4,2):{(3,1):{(0,3):{}},(3,4):{(0,3):{}}}}
-}
backwardSymbolTrieUnder :: Symbol -> BAC -> Maybe (Tree (Symbol, Symbol))
backwardSymbolTrieUnder sym = cofoldUnder sym \_curr results ->
  results
  |> filter (fst .> \(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))
  |> fmap (first symbol2)
  |> Map.fromList
  |> Tree

{- |
Zip all suffixes of given nodes.
It can be used to check lower isomorphisms for given symbols.

Examples:

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffixes [(2,[(1,1),(1,5)]),(4,[(1,3),(1,7)])] crescent
[(1,[1,3]),(1,[5,7]),(0,[2,4])]

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffixes [(3,[(2,1),(4,1)])] crescent
[(2,[1]),(4,[1]),(1,[2]),(1,[6]),(0,[3])]

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffixes [(0,[])] crescent
[]
-}
zipSuffixes ::
  [(Symbol, [(Symbol, Symbol)])]
      -- ^ The symbols to zip and the keys to classify nondecomposable incoming edges.
  -> BAC
  -> Maybe [(Arrow, [Arrow])]
zipSuffixes [] _ = Just []
zipSuffixes tgts_suffix node = do
  guard $
    tgts_suffix
    |> fmap (suffixND node .> fmap symbol2 `bimap` sort)
    |> all (uncurry (==))
  guard $ tgts_suffix |> fmap (snd .> fmap fst) |> allSame

  let zipped_nd_suffix =
        tgts_suffix
        |> fmap snd
        |> transpose
        |> fmap ((head .> fst) &&& fmap snd)

  let tgts = tgts_suffix |> fmap fst

  fromJust $ fromReachable (Just []) $
    node |> foldUnder (head tgts) \curr results -> do
      results' <- results |> traverse sequence

      let collapse = nubSortOn (fmap symbol) do
            (lres, edge) <- results' `zip` edges (target curr)
            let sym0 = symbol curr
            let sym = symbol (curr `join` edge)
            case lres of
              AtInner res ->
                res
                |> filter (fst .> symbol .> (== sym))
                |> fmap (snd .> fmap (join edge))
              _ | sym `elem` tgts ->
                zipped_nd_suffix
                |> filter (fst .> (== sym0))
                |> fmap (snd .> fmap (arrow (target curr) .> fromJust))
              _otherwise -> mzero

      guard $ collapse |> transpose |> all (anySame .> not)

      return $
        results'
        |> mapMaybe fromInner
        |> concat
        |> nubOn (symbol `bimap` fmap symbol)
        |> (++ fmap (curr,) collapse)
