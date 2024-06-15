{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}

module BAC.Fundamental.Zip (
  canonicalizeArrow,
  unifiable,
  unify,
  canonicalizeSuffixND,
  zipSuffixes,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard, mzero)
import Data.Bifunctor (bimap)
import Data.List (nub, sort, sortOn, transpose)
import Data.List.Extra (allSame, anySame, nubSort, nubSortOn)
import Data.Map (Map)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)

import Utils.EqlistSet (canonicalizeGradedEqlistSet)
import Utils.Utils ((.>), (|>))
import BAC.Base
import Data.Foldable (foldl')
import Data.Foldable.Extra (notNull)

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)
-- >>> import Data.Map (elems)


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

unifiable :: Monoid e => BAC e -> Symbol -> Maybe (Map Symbol [Dict])
unifiable node sym = do
  guard $ sym /= base
  tgt_arr <- arrow node sym

  let symbolsND arr =
        target arr
        |> edgesND
        |> nubSortOn symbol
        |> fmap (join arr .> symbol)
        |> sort
  let tgt_symbolsND = symbolsND tgt_arr

  let cand_arrs =
        arrows node
        |> filter ((`locate` sym) .> (/= Inner))
        |> filter (symbol .> (tgt_arr `locate`) .> (/= Inner))
        |> filter (symbolsND .> (== tgt_symbolsND))

  let cand_result = cand_arrs |> fmap (symbol &&& canonicalizeArrow) |> Map.fromList
  let cand_key = Map.fromList $ cand_arrs |> fmap \arr ->
        target arr
        |> edgesND
        |> fmap (dict .> cat (head (cand_result ! symbol arr)))
        |> nubSort
        |> (symbol arr,)
  let key0 = cand_key ! sym

  return $ cand_result |> Map.filterWithKey \sym _ -> cand_key ! sym == key0

{- |
Zip and unify nodes, with parameters @tgts :: [Symbol]@, where `tgts` is a list of symbols
to be zipped.  It will checks if the structures of the target nodes referenced by `tgts`
are the same, and zip target nodes.
-}
unify ::
  Monoid e
  => [Symbol]
  -- ^ The symbol referencing the node and symbols to be zipped.
  -> BAC e
  -> Maybe (BAC e)
unify tgts node = do
  -- ensure that `(src, tgt)` for all `tgt <- tgts` are reachable
  guard $ notNull tgts
  tgt_arrs <- tgts |> traverse (arrow node)

  -- ensure that all dictionaries of arrows to be unified are the same except for base wire
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  -- ensure that all targets of arrows to be merged are the same
  -- due to the previous check, only the first layer need to be checked
  -- the equality of values carried by edges is not checked
  guard $ tgt_arrs |> fmap (target .> edges .> fmap dict) |> allSame

  -- zip target nodes
  let tgt_node' = tgt_arrs |> concatMap (target .> edges) |> BAC
  let replaceNode node tgt =
        fromJust $ fromInner $ node |> modifyUnder tgt \(_curr, edge) -> \case
          AtOuter -> return edge
          AtBoundary -> return edge {target = tgt_node'}
          AtInner res -> return edge {target = res}

  return $ foldl' replaceNode node tgts

canonicalizeSuffixND :: Monoid e => BAC e -> Symbol -> [[(Symbol, Symbol)]]
canonicalizeSuffixND node sym =
  suffixND node sym
  |> nubSortOn symbol2
  |> fmap (\(src_arr, tgt_arr) ->
    arrowsUnder node (symbol src_arr)
    |> fmap (\arr1 -> (arr1, arr1 `divide` src_arr))
    |> concatMap sequence
    |> fmap (\(arr1, arr2) -> (symbol2 (arr1, arr2), symbol2 (arr1, arr2 `join` tgt_arr)))
    |> sortOn fst
    |> fmap snd
    |> (symbol2 (src_arr, tgt_arr) :)
  )
  |> canonicalizeGradedEqlistSet fst
  |> fmap (fmap head)

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
  => [(Symbol, [(Symbol, Symbol)])]
  -- ^ The symbols to zip and the keys to classify nondecomposable incoming edges.
  -> BAC e
  -> Maybe [(Symbol, [Symbol])]
zipSuffixes [] _ = Just []
zipSuffixes tgts_suffix node = do
  guard $
    tgts_suffix
    |> fmap (suffixND node .> fmap symbol2 .> nubSort `bimap` sort)
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

      let collapse = nubSort do
            (lres, edge) <- results' `zip` edges (target curr)
            let sym0 = symbol curr
            let sym = symbol (curr `join` edge)
            case lres of
              AtInner res ->
                res
                |> filter (fst .> (== sym))
                |> fmap (snd .> fmap (dict edge !))
              _ | sym `elem` tgts ->
                zipped_nd_suffix
                |> filter (fst .> (== sym0))
                |> fmap snd
              _otherwise -> mzero

      guard $ collapse |> transpose |> all (anySame .> not)

      return $
        results'
        |> mapMaybe fromInner
        |> concat
        |> nub
        |> (++ fmap (symbol curr,) collapse)
