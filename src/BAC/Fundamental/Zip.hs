{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

module BAC.Fundamental.Zip (
  eqStruct,
  canonicalizeRootNode,
  canonicalizeArrow,
  canonicalizeNode,
  forwardSymbolTrieUnder,
  backwardSymbolTrieUnder,
  zipSuffix,
) where

import Control.Arrow ((&&&))
import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.List (sort, transpose, sortOn)
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
--   The symbol list of nodes should be the same, and equality of child nodes are not
--   checked.  The node with the same structure can be unioned by merging their edges.
eqStruct :: [BAC] -> Bool
eqStruct = fmap edgesND .> fmap (fmap dict) .> allSame

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
  |> fmap (base :)
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
  |> fmap (base :)
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
    |> fmap (base :)
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

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffix [(2,[0,1::Int]),(4,[0,1])] crescent
[(1,[1,3]),(1,[5,7]),(0,[2,4])]

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffix [(3,[0,1::Int])] crescent
[(2,[1]),(4,[1]),(1,[2]),(1,[6]),(0,[3])]

>>> fmap (symbol `bimap` fmap symbol) $ fromJust $ zipSuffix [(0,[]::[Int])] crescent
[]
-}
zipSuffix ::
  Ord k
  => [(Symbol, [k])]
      -- ^ The symbols to zip and the keys to classify nondecomposable incoming edges.
  -> BAC
  -> Maybe [(Arrow, [Arrow])]
zipSuffix [] _ = Just []
zipSuffix tgts_keys node = do
  guard $ tgts_keys |> all (snd .> anySame .> not)
  guard $ tgts_keys |> fmap (snd .> sort) |> allSame
  guard $ tgts_keys |> all (fst .> locate (root node) .> (/= Outer))

  let pars_keys = tgts_keys |> fmap (first (suffixND node))
  guard $ pars_keys |> fmap (fst .> length) |> allSame
  guard $ pars_keys |> fmap (length `bimap` length) |> all (uncurry (==))
  guard $
    pars_keys
    |> fmap (uncurry zip .> sortOn snd .> fmap fst)
    |> transpose
    |> all (fmap (fst .> symbol) .> allSame)

  let zipped_nd_suffix =
        pars_keys
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose
        |> fmap ((head .> fst) &&& fmap snd)

  let tgts = tgts_keys |> fmap fst

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
                |> filter (fst .> symbol .> (== sym0))
                |> fmap snd
              _otherwise -> mzero

      guard $ collapse |> transpose |> all (anySame .> not)

      return $
        results'
        |> mapMaybe fromInner
        |> concat
        |> nubOn (symbol `bimap` fmap symbol)
        |> (++ fmap (curr,) collapse)
