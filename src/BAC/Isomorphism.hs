{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}

module BAC.Isomorphism (
  eqStruct,
  canonicalize,
  canonicalizeObject,
  forwardSymbolTrieUnder,
  backwardSymbolTrieUnder,
  lowerIso,
) where

import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.List (elemIndex, sort, sortOn, transpose)
import Data.List.Extra (allSame, anySame, nubSort)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, mapMaybe)
import Prelude hiding (compare, map)

import Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet)
import Utils.Utils ((.>), (|>))
import BAC.Base

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Map (fromList, elems)
-- >>> import Data.Maybe (fromJust)


-- | Structural equality, the equality of nodes up to rewiring.
--   The symbols of nodes should be the same, and equality of child nodes are not checked.
--   The node with the same structure can be unioned by merging their edges.
eqStruct :: [BAC] -> Bool
eqStruct = fmap edgesND .> fmap (fmap dict) .> allSame

-- | Find mappings to canonicalize the order of symbols of a node.  It will return
--   multiple mappings if it possesses some symmetries.
--   The absolute order has no meaning, but can be used to check the isomorphism between
--   nodes.  The relative order between these mappings forms automorphism of this BAC.
--
--   Examples:
--
--   >>> fmap elems $ canonicalize crescent
--   [[0,1,2,3,4]]
--
--   >>> fmap elems $ canonicalize $ target $ fromJust $ arrow crescent 1
--   [[0,1,2,3,4,5,6],[0,1,2,3,6,5,4],[0,3,2,1,4,5,6],[0,3,2,1,6,5,4],[0,4,5,6,1,2,3],[0,6,5,4,1,2,3],[0,4,5,6,3,2,1],[0,6,5,4,3,2,1]]
canonicalize :: BAC -> [Dict]
canonicalize =
  edgesND
  .> fmap dict
  .> fmap Map.elems
  .> canonicalizeEqlistSet
  .> fmap (base :)
  .> fmap ((`zip` [base..]) .> Map.fromList)

-- | Find mappings to canonicalize the order of symbols of a subnode specified by given
--   symbol.  The induced automorphisms are invariant under the mapping of incoming edges.
--   It can be used to check the upper isomorphism between objects.
--
--   Examples:
--
--   >>> fmap elems $ fromJust $ canonicalizeObject crescent 1
--   [[0,1,2,5,3,4,6],[0,3,4,6,1,2,5]]
canonicalizeObject :: BAC -> Symbol -> Maybe [Dict]
canonicalizeObject node tgt = do
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

-- | Collect all maximum chains to a node into a trie.
--   It is a tree such that its paths correspond to maximum chains, which is represented
--   as a sequence of pairs of symbols, and each pair of symbols indicates a
--   nondecomposable morphism.  Just like BAC, the nodes of this trie is implicitly
--   shared.
--
--   Examples:
--
--   >>> putStr $ showTree $ fromJust $ forwardSymbolTrieUnder 6 cone
--   {(0,3):{(3,1):{(4,2):{}},(3,4):{(4,2):{}}}}
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

-- | Collect all maximum chains to a node into a reversed trie.
--   It is a tree such that its paths correspond to the reverse of maximum chains, which
--   is represented as a sequence of pairs of symbols, and each pair of symbols indicates
--   a nondecomposable morphism.  Just like BAC, the nodes of this trie is implicitly
--   shared.
--
--   Examples:
--
--   >>> putStr $ showTree $ fromJust $ backwardSymbolTrieUnder 6 cone
--   {(4,2):{(3,1):{(0,3):{}},(3,4):{(0,3):{}}}}
backwardSymbolTrieUnder :: Symbol -> BAC -> Maybe (Tree (Symbol, Symbol))
backwardSymbolTrieUnder sym = cofoldUnder sym \_curr results ->
  results
  |> filter (fst .> \(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))
  |> fmap (first symbol2)
  |> Map.fromList
  |> Tree

{- |
Check lower isomorphisms for given symbols.

Examples:

>>> lowerIso [2,4] [[0,1::Int], [0,1]] crescent
True
-}
lowerIso ::
  Eq k
  => [Symbol]  -- ^ The symbols to check.
  -> [[k]]     -- ^ The keys to classify nondecomposable incoming morphisms.
  -> BAC
  -> Bool
lowerIso [] _ _ = True
lowerIso [_] _ _ = True
lowerIso tgts keys node = isJust do
  let tgt_pars = tgts |> fmap (suffixND node)
  guard $ tgt_pars |> fmap length |> allSame
  guard $ length keys == length tgt_pars
  guard $ keys `zip` tgt_pars |> fmap (length `bimap` length) |> all (uncurry (==))

  guard $ keys |> all (anySame .> not)
  indices <- keys |> traverse (traverse (`elemIndex` head keys))
  let merging_symbols =
        zip tgt_pars indices
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose
        |> fmap (fmap symbol2)
  guard $ merging_symbols |> all (fmap fst .> allSame)

  sequence_ $ node |> foldUnder (head tgts) \curr results -> do
    results' <- results |> traverse sequence

    let collapse = nubSort $ fmap sort do
          (lres, edge) <- results' `zip` edges (target curr)
          case lres of
            AtOuter -> mzero
            AtInner res -> res |> fmap (fmap (dict edge !))
            AtBoundary ->
              merging_symbols
              |> filter (head .> fst .> (== symbol curr))
              |> fmap (fmap snd)

    guard $ collapse |> concat |> anySame |> not

    return collapse
