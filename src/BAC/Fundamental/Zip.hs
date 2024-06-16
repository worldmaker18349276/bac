{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}

module BAC.Fundamental.Zip (
  canonicalizeArrow,
  canonicalMapping,
  UnifyKey,
  unifyKey,
  unifiable,
  unifyNodes,
  canonicalizeSuffixND,
  ZipKey,
  zipKey,
  zippable,
  zipSuffixes,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard, mzero)
import Data.Bifunctor (bimap)
import Data.Foldable (foldl')
import Data.Foldable.Extra (notNull)
import Data.List (elemIndex, mapAccumL, nub, sort, sortOn, transpose)
import Data.List.Extra (allSame, anySame, nubSort, nubSortOn, snoc)
import Data.Map (Map)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)

import Utils.EqlistSet (canonicalizeGradedEqlistSet)
import Utils.Utils ((.>), (|>))
import BAC.Base

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)
-- >>> import Data.Map (elems)


{- |
Find all possible orders of nondecomposable symbols to canonicalize the order of symbols
of the target node of an arrow.  Use `canonicalMapping` to obtain the relabel mapping.
The induced automorphisms are invariant under the mapping of the arrow.

Examples:

>>> fmap elems $ canonicalizeArrow $ fromJust $ arrow crescent 1
[[0,1,2,5,3,4,6],[0,3,4,6,1,2,5]]
-}
canonicalizeArrow :: Arrow e -> [[Symbol]]
canonicalizeArrow arr =
  target arr
  |> edgesND
  |> nubSortOn symbol
  |> fmap dict
  |> fmap Map.elems
  |> canonicalizeGradedEqlistSet (dict arr !)
  |> fmap (fmap head)

{- |
Make a mapping based on given order of nondecomposable symbols (obtained by
`canonicalizeArrow`) to canonicalize the order of symbols of the target node of given
arrow.
-}
canonicalMapping :: Arrow e -> [Symbol] -> Dict
canonicalMapping arr =
  concatMap (dicts !) .> nub .> (base :) .> (`zip` [base..]) .> Map.fromList
  where
  dicts = target arr |> edges |> fmap dict |> fmap Map.elems |> fmap (\s -> (head s, s)) |> Map.fromList

newtype UnifyKey =
  UnifyKey
  [( Symbol -- ^ identity (symbol from the root node) of the target node of a nondecomposable outgoing edge
  , [Symbol] -- ^ relabelled value list of dictionary of this edge
  )]
  deriving (Eq, Ord, Show)

{- |
Get canonical key based on a canonical order to check if canonicalized nodes can be
unified.  Any valid canonical order obtained by `canonicalizeArrow` should have the same
key.
It can be used to check the upper isomorphism between objects.
-}
unifyKey :: Monoid e => Arrow e -> [Symbol] -> UnifyKey
unifyKey arr canonical_order =
  target arr
  |> edgesND
  |> fmap (\edge -> (dict arr ! symbol edge, mapping `cat` dict edge))
  |> nubSortOn fst
  |> fmap (fmap Map.elems)
  |> UnifyKey
  where
  mapping = canonicalMapping arr canonical_order

{- |
Find all possible nodes they can be unified with a given symbol, and compute canonical
orders for them.
-}
unifiable :: Monoid e => BAC e -> Symbol -> Maybe (Map Symbol [[Symbol]])
unifiable node tgt = do
  guard $ tgt /= base
  tgt_arr <- arrow node tgt

  let childrenND arr =
        target arr
        |> edgesND
        |> nubSortOn symbol
        |> fmap (join arr .> symbol)
        |> sort
  let tgt_childrenND = childrenND tgt_arr

  let cand_arrs =
        arrows node
        |> filter ((`locate` tgt) .> (/= Inner))
        |> filter (symbol .> (tgt_arr `locate`) .> (/= Inner))
        |> filter (childrenND .> (== tgt_childrenND))

  let cand_result = cand_arrs |> fmap (symbol &&& canonicalizeArrow) |> Map.fromList
  let cand_key =
        cand_arrs
        |> fmap (\arr -> (symbol arr, unifyKey arr (head (cand_result ! symbol arr))))
        |> Map.fromList
  let key0 = cand_key ! tgt

  return $ cand_result |> Map.filterWithKey \sym _ -> cand_key ! sym == key0

{- |
Zip and unify nodes, with parameters @tgts :: [Symbol]@, where `tgts` is a list of symbols
to be zipped.  It will checks if the structures of the target nodes referenced by `tgts`
are the same, and zip target nodes.
-}
unifyNodes ::
  Monoid e
  => [Symbol]
  -- ^ The symbols referencing the nodes to be zipped.
  -> BAC e
  -> Maybe (BAC e)
unifyNodes tgts node = do
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
        fromJust $ fromInner $ root node |> modifyUnder tgt \(_curr, edge) -> \case
          AtOuter -> return edge
          AtBoundary -> return edge {target = tgt_node'}
          AtInner res -> return edge {target = res}

  return $ foldl' replaceNode node tgts


rdict :: Monoid e => BAC e -> (Arrow e, Arrow e) -> [((Symbol, Symbol), (Symbol, Symbol))]
rdict node (src_arr, tgt_arr) =
  arrowsUnder node (symbol src_arr)
  |> fmap (\arr1 -> (arr1, arr1 `divide` src_arr))
  |> concatMap sequence
  |> fmap (\(arr1, arr2) -> (symbol2 (arr1, arr2), symbol2 (arr1, arr2 `join` tgt_arr)))
  |> sortOn fst
  |> (((symbol src_arr, base), symbol2 (src_arr, tgt_arr)) :)

{- |
Find order of nondecomposable incoming edges to canonicalize the order of suffixes of the
arrow to the target node.
-}
canonicalizeSuffixND :: Monoid e => BAC e -> Symbol -> [[(Symbol, Symbol)]]
canonicalizeSuffixND node sym =
  suffixND node sym
  |> nubSortOn symbol2
  |> fmap (rdict node .> fmap snd)
  |> canonicalizeGradedEqlistSet fst
  |> fmap (fmap head)

newtype ZipKey =
  ZipKey
  [( Symbol -- ^ identity (symbol from the root node) of the source node of a nondecomposable incoming edge
  , [Int] -- ^ relabelled value list of reversed dictionary of this edge
  )]
  deriving (Eq, Ord, Show)

{- |
Get canonical key based on a canonical order to check if canonicalized nodes can be
zipped.  Any valid canonical order obtained by `canonicalizeSuffixND` should have the same
key.
It can be used to check the lower isomorphism between objects.
-}
zipKey :: Monoid e => BAC e -> Symbol -> [(Symbol, Symbol)] -> ZipKey
zipKey node sym canonical_order =
  suffixND node sym
  |> nubSortOn (\arr2 -> elemIndex (symbol2 arr2) canonical_order)
  |> fmap (rdict node .> fmap snd)
  |> mapAccumL (\accum list -> relabelList accum list |> fmap (fst (head list),)) []
  |> snd
  |> ZipKey
  where
  relabelList :: Eq a => [a] -> [a] -> ([a], [Int])
  relabelList = relabelList' []
  relabelList' :: Eq a => [Int] -> [a] -> [a] -> ([a], [Int])
  relabelList' res accum [] = (accum, res)
  relabelList' res accum (h:t) =
    case elemIndex h accum of
      Just i -> relabelList' (res `snoc` i) accum t
      Nothing -> relabelList' (res `snoc` length accum) (accum `snoc` h) t

{- |
Find all possible nodes they can be zipped with a given node, and compute canonical orders
for them.
-}
zippable :: Monoid e => BAC e -> Symbol -> Maybe (Map Symbol [[(Symbol, Symbol)]])
zippable node tgt = do
  guard $ tgt /= base
  tgt_arr <- arrow node tgt

  let parentsND = symbol .> suffixND node .> fmap symbol2 .> nubSort .> fmap fst .> sort
  let tgt_parentsND = parentsND tgt_arr

  let cand_syms =
        arrows node
        |> filter ((`locate` tgt) .> (/= Inner))
        |> filter (symbol .> (tgt_arr `locate`) .> (/= Inner))
        |> filter (parentsND .> (== tgt_parentsND))
        |> fmap symbol

  let cand_result = cand_syms |> fmap (id &&& canonicalizeSuffixND node) |> Map.fromList
  let cand_key =
        cand_syms
        |> fmap (\sym -> (sym, zipKey node sym (head (cand_result ! sym))))
        |> Map.fromList
  let key0 = cand_key ! tgt

  return $ cand_result |> Map.filterWithKey \sym _ -> cand_key ! sym == key0

{- |
Zip all suffixes of given nodes.

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
    root node |> foldUnder (head tgts) \curr results -> do
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
