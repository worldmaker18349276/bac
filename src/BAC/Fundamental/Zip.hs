{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module BAC.Fundamental.Zip (
  eqStruct,
  zipArrows,
  canonicalizeRootNode,
  canonicalizeArrow,
  canonicalizeNode,
  zipSuffixes,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard, mzero)
import Data.Bifunctor (bimap)
import Data.List (sort, transpose, nub)
import Data.List.Extra (allSame, anySame, nubSortOn, nubOn, nubSort)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Prelude hiding (compare, map)

import Utils.EqlistSet (canonicalizeGradedEqlistSet)
import Utils.Utils ((.>), (|>))
import BAC.Base
import Data.Foldable.Extra (notNull)

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)
-- >>> import Data.Map (elems)


-- | Structural equality, the equality of nodes up to rewiring.
--   Nodes should have the same symbol list, and equality of child nodes are not checked.
--   The node with the same structure can be unioned by merging their edges.
eqStruct :: [BAC e] -> Bool
eqStruct = fmap edgesND .> fmap (nubSortOn symbol) .> fmap (fmap dict) .> allSame

{- |
Zip arrows of BACs, which shows the equality of nodes up to rewiring and relabeling.
Also, the equality of child nodes are not checked.  The correspondence between
nondecomposable edges of the root nodes should be provided.
-}
zipArrows :: Monoid e => [(BAC e, [Symbol])] -> Maybe [[Arrow e]]
zipArrows nodes_prefix = do
  -- check the given nondecomposable symbols
  guard $
    nodes_prefix
    |> fmap (edgesND .> fmap symbol .> nubSort `bimap` sort)
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
  -- dictionaries should become the same after relabeling
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
canonicalizeRootNode :: (Monoid e, Ord e) => BAC e -> [Dict]
canonicalizeRootNode node =
  node
  |> edgesND
  |> nubSortOn symbol
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
canonicalizeArrow :: Arrow e -> [Dict]
canonicalizeArrow arr =
  target arr
  |> edgesND
  |> nubSortOn symbol
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
canonicalizeNode :: Monoid e => BAC e -> Symbol -> Maybe [Dict]
canonicalizeNode node tgt = do
  guard $ tgt /= base
  tgt_arr <- arrow node tgt
  let keys =
        tgt
        |> suffixND node
        |> nubSortOn symbol2
        |> fmap (snd .> dict .> fmap (: []))
        |> foldl (Map.unionWith (++)) Map.empty
  return $
    target tgt_arr
    |> edgesND
    |> nubSortOn symbol
    |> fmap dict
    |> fmap Map.elems
    |> canonicalizeGradedEqlistSet (keys !)
    |> fmap (concat .> nub .> (base :))
    |> fmap ((`zip` [base..]) .> Map.fromList)

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
  Monoid e
  => BAC e
  -> [(Symbol, [Symbol])]
  -- ^ The group of list of nondecomposable incoming edges to zip.
  -> Maybe [(Symbol, [Symbol])]
zipSuffixes node suffixes = do
  -- the i-th arrow to merge for each group should have the same target
  guard $ suffixes |> all (snd .> notNull)
  guard $ suffixes |> fmap (snd .> length) |> allSame
  tgt_arrs <- suffixes
    |> fmap sequence
    |> traverse (traverse (arrow2 node .> fmap (uncurry join)))
  guard $
    tgt_arrs
    |> transpose
    |> all (fmap symbol .> allSame)
  guard $
    tgt_arrs
    |> head
    |> fmap symbol
    |> anySame
    |> not

  -- evrey nondecomposable incoming edges should be zipped exactly once
  guard $ head tgt_arrs
    |> fmap (symbol .> suffixND node .> fmap symbol2 .> nubSort)
    |> zip (suffixes |> fmap sequence |> transpose |> fmap sort)
    |> all (uncurry (==))

  let tgts = head tgt_arrs |> fmap symbol

  fromJust $ fromReachable (Just []) $
    node |> foldUnder (head tgts) \curr results -> do
      results' <- results |> traverse sequence

      -- collapse is a set of merge lists of symbols
      let collapse = nubSort do
            (lres, edge) <- results' `zip` edges (target curr)
            let sym0 = symbol curr
            let sym = symbol (curr `join` edge)
            case lres of
              -- map merge lists of children into this node
              AtInner res ->
                res
                |> filter (fst .> (== sym))
                |> fmap (snd .> fmap (dict edge !))
              -- user specified merge lists
              _ | sym `elem` tgts ->
                suffixes
                |> filter (fst .> (== sym0))
                |> fmap snd
              _otherwise -> mzero

      -- merge lists should have distinct symbols
      guard $ collapse |> concat |> anySame |> not

      -- append to result
      return $
        results'
        |> mapMaybe fromInner
        |> concat
        |> nub
        |> (++ fmap (symbol curr,) collapse)
