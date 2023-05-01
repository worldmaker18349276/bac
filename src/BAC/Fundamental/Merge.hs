{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Merge (
  mergeSymbols,
  mergeSymbolsOnRoot,
  mergeNodes,
  mergeRootNodes,
  expandMergingSymbols,
  mergeSymbolsAggressively,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable.Extra (notNull)
import Data.List.Extra (allSame, anySame, groupSortOn)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)

import BAC.Base
import BAC.Fundamental.Zip
import Utils.Utils ((.>), (|>))
import Data.Foldable (find)
import Utils.DisjointSet (bipartiteEqclass)
import Data.List (sort)

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Merge symbols on a node, with arguments @(src, tgts) :: (Symbol, [Symbol])@ and
@sym :: Symbol@, where @src@ is the symbol referencing the source node, `tgts` is a list
of symbols to be merged, and `sym` is the merged symbol.  When merging symbols on the root
node, it will checks if the structures of the target nodes referenced by `tgts` are the
same.  Users should unify target nodes before merging.

In categorical perspectives, it merges non-terminal morphisms, where @(src, tgt)@ for
@tgt <- tgts@ indicate the morphism to merge, and @(src, sym)@ will indicates the merged
morphism.

Examples:

>>> printBAC $ fromJust $ mergeSymbols (1,[2,3,6,8]) 2 torus
- 0->1; 1->2; 2->3; 4->5; 7->2; 10->5
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->4; 1->2; 2->2
    &2
    - 0->1
      *1
    - 0->2
      *1
  - 0->7; 1->2; 2->2
    *0
  - 0->10; 1->2; 2->2
    *2
-}
mergeSymbols ::
  (Symbol, [Symbol])  -- ^ The symbol referencing the node and symbols to be merged.
  -> Symbol           -- ^ The new symbol after merging.
  -> BAC
  -> Maybe BAC
mergeSymbols (src, tgts) sym node = do
  guard $ notNull tgts
  src_arr <- arrow node src
  tgt_arrs <- tgts |> traverse (arrow (target src_arr))
  guard $ src_arr |> target |> symbols |> filter (`notElem` tgts) |> notElem sym
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  guard $
    src /= base
    || (tgt_arrs |> fmap (target .> edges .> fmap dict) |> allSame)
  guard $ suffix node src |> all \(_, edge) -> tgts |> fmap (dict edge !) |> allSame

  let merge s = if s `elem` tgts then sym else s

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let dict' = dict edge |> Map.toList |> fmap (second merge) |> Map.fromList
        return edge {dict = dict'}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict', target = res0}
      where
      dict' = dict edge |> Map.toList |> fmap (first merge) |> Map.fromList

mergeSymbolsOnRoot :: [Symbol] -> Symbol -> BAC -> Maybe BAC
mergeSymbolsOnRoot tgts = mergeSymbols (base, tgts)

{- |
Merge nodes, with arguments @tgts_keys :: [(Symbol, [k])]@ and
@merger :: (Symbol, [Symbol]) -> Symbol@, where `tgts_keys` contains nodes to merge and
the keys indicating correspondence among their nondecomposable incoming edges, and
`merger` is the function to merge symbols on all ancestor nodes.  The nondecomposable
incoming edges of the nodes to merge will be paired up by function
`BAC.Fundamental.zipSuffix` according to the keys.

In categorical perspectives, it merges terminal morphisms.  Where `tgt` for
@(tgt, _) <- tgts_keys@ indicates the source object of terminal morphisms to merge.  All
incoming morphisms of these objects, say @(s, [r1, r2, ...])@, will be merged into the
morphism indicated by pair of symbol @(s, merger (s, [r1, r2, ...]))@.

Examples:

>>> crescent' = fromJust $ alterSymbol (2,1) 2 crescent
>>> printBAC $ fromJust $ mergeNodes [(2,[False,True]),(4,[False,True])] (snd .> head) crescent'
- 0->1; 1->2; 2->3; 5->2; 6->3
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->5; 1->6; 2->6
    *0
-}
mergeNodes ::
  Ord k
  => [(Symbol, [k])]   -- ^ The symbols referencing the nodes to be merged and the keys to
                       --   classify nondecomposable incoming morphisms.
  -> ((Symbol, [Symbol]) -> Symbol)
                       -- ^ The merger of symbols.
  -> BAC
  -> Maybe BAC
mergeNodes tgts_keys merger node = do
  guard $ notNull tgts_keys
  guard $ tgts_keys |> fmap fst |> anySame |> not

  zipped_suffix <- zipSuffix tgts_keys node
  guard $
    zipped_suffix
    |> groupSortOn (fst .> symbol)
    |> fmap ((head .> fst) &&& fmap snd)
    |> all \(curr, groups) ->
      let
        sym0 = symbol curr
        syms = groups |> concat |> fmap symbol
        syms' = groups |> fmap (fmap symbol .> (sym0,) .> merger)
      in
        curr
        |> target
        |> symbols
        |> filter (`notElem` syms)
        |> (++ syms')
        |> anySame
        |> not

  let tgts = tgts_keys |> fmap fst
  let tgt_nodes = tgts |> fmap (arrow node .> fromJust .> target)
  merged_node <- mergeRootNodes tgt_nodes

  let merged_syms_dicts = Map.fromList do
        (curr, arrs) <- zipped_suffix
        let sym0 = symbol curr
        let syms = fmap symbol arrs
        let sym' = merger (sym0, syms)
        let merged_dict =
              arrs
              |> fmap dict
              |> foldl Map.union Map.empty
              |> Map.insert base sym'
        sym <- syms
        return ((sym0, sym), (sym', merged_dict))

  fromReachable node $
    node |> foldUnder (head tgts) \curr results -> fromEdges do
      (res, edge) <- results `zip` edges (target curr)
      let sym0 = symbol curr
      let sym = symbol (curr `join` edge)
      let collapsed_node =
            if sym `elem` tgts
            then merged_node
            else res |> fromInner |> fromMaybe (target edge)
      let collapsed_dict =
            if sym `elem` tgts
            then snd (merged_syms_dicts ! (sym0, symbol edge))
            else
              dict edge
              |> Map.toList
              |> fmap (\(s1, s2) ->
                (
                  Map.lookup (sym, s1) merged_syms_dicts |> maybe s1 fst,
                  Map.lookup (sym0, s2) merged_syms_dicts |> maybe s2 fst
                )
              )
              |> Map.fromList
      return edge {dict = collapsed_dict, target = collapsed_node}

{- |
Merge root nodes (merge BACs), with an argument `nodes :: [BAC]` indicating the nodes to
merged, which should have disjoint symbol lists except the base symbol.

Examples:

>>> printBAC $ fromJust $ mergeRootNodes [fromJust $ singleton 1, empty, fromJust $ singleton 2]
- 0->1
- 0->2

>>> printBAC $ fromJust $ mergeRootNodes [fromJust $ singleton 6, crescent]
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
- 0->6
-}
mergeRootNodes :: [BAC] -> Maybe BAC
mergeRootNodes nodes = do
  guard $ nodes |> fmap (symbols .> filter (/= base)) |> concat |> anySame |> not
  return $ nodes |> concatMap edges |> fromEdges


expandMergingSymbols :: BAC -> [[Symbol]] -> [[Symbol]]
expandMergingSymbols node =
  fmap (fmap (arrow node .> fromJust .> dict .> Map.toList))
  .> zip [0 :: Integer ..]
  .> concatMap sequence
  .> concatMap sequence
  .> fmap (\(a, (b, c)) -> ((a, b), c))
  .> bipartiteEqclass
  .> fmap snd
  .> filter (length .> (> 1))
  .> fmap sort
  .> sort

mergeSymbolsAggressively ::
  (Symbol, [[Symbol]]) -> ((Symbol, [Symbol]) -> Symbol) -> BAC -> Maybe BAC
mergeSymbolsAggressively (src, tgts) merger node = do
  src_arr <- arrow node src

  tgt_arrs <- tgts |> traverse (traverse (arrow (target src_arr)))
  guard $ tgt_arrs |> all (fmap target .> allSame)

  let validateMerger curr merging_lists =
        target curr
        |> symbols
        |> filter (`notElem` concat merging_lists)
        |> (++ fmap ((symbol curr,) .> merger) merging_lists)
        |> anySame
        |> not

  let merging_lists = expandMergingSymbols (target src_arr) tgts
  guard $ validateMerger src_arr merging_lists

  let mergeSymbol (src', tgts') s = tgts' |> find (elem s) |> maybe s ((src',) .> merger)
  let merged_node = fromEdges do
        edge <- target src_arr |> edges
        let merged_dict = dict edge |> fmap (mergeSymbol (src, merging_lists))
        return edge {dict = merged_dict}
  let res0 = (merged_node, merging_lists)

  lres <- sequence $
    node |> foldUnder src \curr results -> do
      let sym0 = symbol curr
      results' <-
        traverse sequence results
        |> fmap (fmap (fromReachable res0 .> maybe (Nothing, []) (first Just)))
      let merging_lists =
            target curr
            |> edges
            |> fmap dict
            |> (`zip` fmap snd results')
            |> concatMap (sequence .> fmap (sequence .> fmap (uncurry (!))))
            |> expandMergingSymbols (target curr)
      guard $ validateMerger curr merging_lists

      let merged_node = fromEdges do
            ((lres, merging_lists'), edge) <- results' `zip` edges (target curr)
            let sym = symbol (curr `join` edge)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol (sym0, merging_lists))
                  |> Map.mapKeys (mergeSymbol (sym, merging_lists'))
            let res = fromMaybe (target edge) lres
            return edge {dict = merged_dict, target = res}
      return (merged_node, merging_lists)

  fromReachable res0 lres |> fmap fst

