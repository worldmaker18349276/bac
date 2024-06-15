{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module BAC.Fundamental.Merge (
  mergeSymbols,
  mergeSymbolsOnRoot,
  mergeNodes,
  mergeRootNodes,
  -- expandMergingSymbols,
  -- mergeSymbolsAggressively,
  -- mergeSymbolsOnRootAggressively,
) where

import Control.Arrow ((&&&))
import Control.Monad (guard)
import Data.Bifunctor (first)
import Data.Foldable (find)
import Data.Foldable.Extra (notNull)
import Data.List (sort)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, snoc)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe)

import BAC.Base
import BAC.Fundamental.Zip (zipSuffixes)
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils (asserted, (.>), (|>))

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Merge symbols on a node, with parameters @(src, tgts) :: (Symbol, [Symbol])@ and
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

>>> crescent_1 = arrow crescent 1 |> fromJust |> target
>>> printBAC $ fromJust $ mergeSymbols (0,[1,3]) 1 crescent_1
- 0->1; 1->2
  - 0->1
- 0->5; 1->6
  - 0->1
    &0
- 0->7; 1->6
  - 0->1
    *0

>>> mergeSymbols (0,[1,5]) 1 crescent_1
Nothing
-}
mergeSymbols ::
  Monoid e
  => (Symbol, [Symbol])
  -- ^ The symbol referencing the node and symbols to be merged.
  -> Symbol
  -- ^ The new symbol after merging.
  -> BAC e
  -> Maybe (BAC e)
mergeSymbols (src, tgts) sym node = do
  -- ensure that `(src, tgt)` for all `tgt <- tgts` are reachable
  guard $ notNull tgts
  src_arr <- arrow node src
  let src_node = target src_arr
  tgt_arrs <- tgts |> traverse (arrow src_node)

  -- validate merging symbols `tgts` -> `sym`
  guard $ src_node |> symbols |> filter (`notElem` tgts) |> (`snoc` sym) |> anySame |> not
  -- ensure that all dictionaries of arrows to be merged are the same except for base wire
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  -- ensure that all targets of arrows to be merged are the same
  -- it is needed only when `src == base`
  -- due to the previous check, only the first layer need to be checked
  -- the equality of values carried by edges is not checked
  guard $
    src /= base
    || (tgt_arrs |> fmap (target .> edges .> fmap dict) |> allSame)
  -- ensure that all symbols to be merged always map to the same symbol
  guard $ suffix node src |> all \(_, edge) ->
    tgts |> fmap (dict edge !) |> allSame

  -- merge symbols on `src_node`
  let merge s = if s `elem` tgts then sym else s
  let src_node' = BAC do
        edge <- edges src_node
        let dict' = dict edge |> Map.map merge
        return edge {dict = dict'}

  fromReachable src_node' $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {dict = dict', target = src_node'}
      where
      dict' = dict edge |> Map.mapKeys merge

-- | Merge symbols on the root node (merge initial morphisms).  See `mergeSymbols` for
--   details.
mergeSymbolsOnRoot :: Monoid e => [Symbol] -> Symbol -> BAC e -> Maybe (BAC e)
mergeSymbolsOnRoot tgts = mergeSymbols (base, tgts)

{- |
Merge nodes, with parameters @tgts_suffix :: [(Symbol, [(Symbol, Symbol)])]@ and @merger
:: (Symbol, [Symbol]) -> Symbol@, where `tgts_suffix` contains nodes to merge and their
nondecomposable incoming edges to zip, and `merger` is the function to merge symbols on
all ancestor nodes.  The nondecomposable incoming edges of the nodes to merge will be
paired up by function `BAC.Fundamental.zipSuffix` according to the order of list.  The
nodes to merge should have distinct symbol lists except base symbol.

In categorical perspectives, it merges terminal morphisms.  Where `tgt` for
@(tgt, _) <- tgts_suffix@ indicates the source object of terminal morphisms to merge.  All
incoming morphisms of these objects, say @(s, [r1, r2, ...])@, will be merged into the
morphism indicated by pair of symbol @(s, merger (s, [r1, r2, ...]))@.

Examples:

>>> crescent' = crescent |> alterSymbol (2,1) 2 |> fromJust
>>> printBAC $ fromJust $ mergeNodes [(2,[(1,1),(1,5)]),(4,[(1,3),(1,7)])] (snd .> head) crescent'
- 0->1; 1->2; 2->3; 5->2; 6->3
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->5; 1->6; 2->6
    *0

>>> torus' = torus |> alterSymbol (2,1) 3 |> fromJust |> alterSymbol (2,2) 4 |> fromJust
>>> printBAC $ fromJust $ mergeNodes [(2,[(1,1),(1,7)]), (5,[(1,4),(1,10)])] (snd .> head) torus'
- 0->1; 1->2; 2->3; 3->3; 6->3; 7->2; 8->3
  - 0->1; 1->3; 2->6; 3->2; 4->3
    &0
    - 0->1
      &1
    - 0->2
      *1
    - 0->3
      *1
    - 0->4
      *1
  - 0->7; 1->2; 2->8; 3->8; 4->6
    *0
-}
mergeNodes ::
  Monoid e
  => [(Symbol, [(Symbol, Symbol)])]
  -- ^ The symbols referencing the nodes to merge and the nondecomposable incoming
  --   morphisms to zip.
  -> ((Symbol, [Symbol]) -> Symbol)
  -- ^ The merger of symbols.
  -> BAC e
  -> Maybe (BAC e)
mergeNodes tgts_suffix merger node = do
  -- ensure that `tgts` are distinct and reachable
  let tgts = tgts_suffix |> fmap fst
  guard $ notNull tgts
  guard $ tgts |> anySame |> not
  tgt_nodes <- tgts |> traverse (arrow node .> fmap target)

  -- zip suffixes
  zipped_suffix <- zipSuffixes tgts_suffix node

  -- validate merger
  guard $
    zipped_suffix
    |> groupSortOn fst
    |> fmap ((head .> fst) &&& fmap snd)
    |> all \(sym0, groups) ->
      arrow node sym0
      |> fromJust
        |> target
        |> symbols
      |> filter (`notElem` concat groups)
      |> (++ fmap ((sym0,) .> merger) groups)
        |> anySame
        |> not

  -- merge nodes of `tgts`, where they should have distinct `symbols` except `base`
  merged_node <- mergeRootNodes tgt_nodes

  -- map suffixes to merged dict
  let merged_dicts = Map.fromList do
        (sym0, syms) <- zipped_suffix
        let merged_sym = merger (sym0, syms)
        let node0 = arrow node sym0 |> fromJust |> target
        let merged_dict =
              syms
              |> fmap (arrow node0 .> fromJust)
              |> fmap dict
              |> foldl Map.union Map.empty
              |> Map.insert base merged_sym
        sym <- syms
        return ((sym0, sym), merged_dict)

  fromReachable node $
    node |> foldUnder (head tgts) \curr results -> BAC do
      (subnode, edge) <- results `zip` edges (target curr)
      let sym0 = symbol curr
      let sym = symbol (curr `join` edge)
      if sym `elem` tgts
      then
        -- a direct edge to the target
        return edge {dict = merged_dicts ! symbol2 (curr, edge), target = merged_node}
      else
        let
          -- an edge between nodes under the target => merge symbols of keys and values
          -- of the original dictionary
          collapsed_node = subnode |> fromInner |> fromMaybe (target edge)
          collapsed_dict =
            dict edge
            |> Map.toList
            |> fmap (\(s1, s2) ->
              if dict curr ! s2 `elem` tgts
              then
                (merged_dicts ! (sym, s1) ! base, merged_dicts ! (sym0, s2) ! base)
              else
                (s1, s2)
            )
            |> nubSort
            |> asserted (fmap fst .> anySame .> not)
            |> Map.fromList
        in
          return edge {dict = collapsed_dict, target = collapsed_node}

{- |
Merge root nodes (merge BACs), with a parameter `nodes :: [BAC]` indicating the nodes to
merge, which should have disjoint symbol lists except the base symbol.

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
mergeRootNodes :: [BAC e] -> Maybe (BAC e)
mergeRootNodes nodes = do
  guard $ nodes |> concatMap (symbols .> filter (/= base)) |> anySame |> not
  return $ nodes |> concatMap edges |> BAC


expandMergingSymbols :: Monoid e => BAC e -> [[Symbol]] -> [[Symbol]]
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
  Monoid e => (Symbol, [[Symbol]]) -> ((Symbol, [Symbol]) -> Symbol) -> BAC e -> Maybe (BAC e)
mergeSymbolsAggressively (src, tgts) merger node = do
  src_arr <- arrow node src

  tgt_arrs <- tgts |> traverse (traverse (arrow (target src_arr)))
  -- guard $ tgt_arrs |> all (fmap target .> allSame)
  guard $ tgt_arrs |> all (fmap (join src_arr .> symbol) .> allSame)

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
  let merged_node = BAC do
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

      let merged_node = BAC do
            ((subnode, merging_lists'), edge) <- results' `zip` edges (target curr)
            let sym = symbol (curr `join` edge)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol (sym0, merging_lists))
                  |> Map.mapKeys (mergeSymbol (sym, merging_lists'))
            return edge {dict = merged_dict, target = subnode |> fromMaybe (target edge)}
      return (merged_node, merging_lists)

  fromReachable res0 lres |> fmap fst

mergeSymbolsOnRootAggressively ::
  Monoid e => [[Symbol]] -> ((Symbol, [Symbol]) -> Symbol) -> BAC e -> Maybe (BAC e)
mergeSymbolsOnRootAggressively tgts = mergeSymbolsAggressively (base, tgts)
