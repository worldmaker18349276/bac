{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module BAC.Algorithm where

import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (traverse_)
import Data.List (delete, elemIndices, findIndex, nub, sort, sortOn, transpose)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe, fromJust, fromMaybe)

import Utils.Utils ((|>), (.>), both, nubOn, groupOn, filterMaybe, distinct, allSame, allSameBy, label)
import Utils.DisjointSet (bipartiteEqclass)
import BAC.Base

empty :: Node e
empty = Node {edges = []}

singleton :: e -> Node e
singleton val = Node {edges = [new_edge]}
  where
  new_sym = 1
  new_dict = Map.singleton base new_sym
  new_node = Node {edges = []}
  new_edge = Arrow' {dict = new_dict, node = new_node, value = val}

removeMorphism :: (Symbol, Symbol) -> Node e -> Maybe (Node e)
removeMorphism (src, tgt) bac = do
  src_arr <- bac |> arrow src
  edges (node src_arr) |> traverse_ \edge -> do
    guard $ symbol edge == tgt || tgt `notElem` dict edge

  let filtered_edges =
        edges (node src_arr) |> filter (\edge -> symbol edge /= tgt)
  let res0 = Node filtered_edges
  guard $ symbols res0 == (symbols (node src_arr) |> delete tgt)

  located_res <- sequence $
    bac |> foldUnder src \curr results -> do
      results' <- traverse sequence results

      let bac = Node do
            (res, edge) <- results' `zip` edges (node curr)
            case res of
              AtOuter -> [edge]
              AtInner res -> [edge {node = res}]
              AtBoundary -> [edge {dict = filtered_dict, node = res0}]
                where
                filtered_dict = dict edge |> Map.delete tgt
      guard $ symbols bac == symbols (node curr)
      Just bac

  fromReachable res0 located_res

removeObject :: Symbol -> Node e -> Maybe (Node e)
removeObject tgt bac = do
  guard $ root bac |> locate tgt |> (== Inner)
  tgt_arr <- bac |> arrow tgt
  guard $ edges (node tgt_arr) |> null

  fromReachable (node tgt_arr) $ bac |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> [edge]
    AtBoundary -> []
    AtInner res -> [edge {dict = filtered_dict, node = res}]
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

prepareForAddingMorphism ::
  Symbol -> Symbol
  -> [(Symbol, Symbol)] -> [(Symbol, Symbol)]
  -> e
  -> Node e -> Maybe (Edge e, Map (Symbol, Symbol) (Symbol, Symbol))
prepareForAddingMorphism src tgt src_alts tgt_alts val bac = do
  src_arr <- bac |> arrow src
  tgt_arr <- bac |> arrow tgt
  guard $ tgt_arr |> locate src |> (== Outer)

  let new_sym = node src_arr |> symbols |> maximum |> (+ 1)

  let children tgt bac = do
        tgt_arr <- bac |> arrow tgt
        Just $ edges (node tgt_arr) |> fmap (tgt_arr,) |> sortOn symbol2
  src_inedges <- bac |> parents src
  tgt_outedges <- bac |> children tgt
  src_outedges' <- src_alts |> traverse (`arrow2` bac)
  tgt_inedges' <- tgt_alts |> traverse (`arrow2` bac)

  guard $ length src_inedges == length tgt_inedges'
  guard $ length tgt_outedges == length src_outedges'

  src_outedges' `zip` tgt_outedges |> traverse_ \((arr1', edge1'), (arr1, edge1)) -> do
    guard $ dict arr1 == dict tgt_arr
    guard $ dict arr1' == dict src_arr
    guard $ dict arr1' `cat` dict edge1' == dict arr1 `cat` dict edge1
  src_inedges `zip` tgt_inedges' |> traverse_ \((arr2, edge2), (arr2', edge2')) -> do
    guard $ dict arr2' == dict arr2
    guard $ dict arr2 `cat` dict edge2 == dict tgt_arr
    guard $ dict arr2' `cat` dict edge2' == dict tgt_arr
  src_outedges' `zip` tgt_outedges |> traverse_ \((arr1', edge1'), (arr1, edge1)) -> do
    src_inedges `zip` tgt_inedges' |> traverse_ \((arr2, edge2), (arr2', edge2')) -> do
      guard $ dict edge2 `cat` dict edge1' == dict edge2' `cat` dict edge1

  new_dict <-
    tgt_outedges
    |> fmap (second (\arr -> arr {value = ()}))
    |> (`zip` src_outedges')
    |> concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
    |> sort
    |> nub
    |> ((base, new_sym) :)
    |> filterMaybe (fmap fst .> distinct)
    |> fmap Map.fromList
  let new_edge = Arrow' {dict = new_dict, node = node tgt_arr, value = val}

  let new_wires =
        src_inedges
        |> fmap (second (\arr -> arr {value = ()}))
        |> (`zip` tgt_inedges')
        |> fmap (both symbol2)
        |> fmap (second $ snd .> (new_sym,))
        |> Map.fromList

  sequence_ $ bac |> foldUnder src \curr results -> do
    results' <- traverse sequence results
    let pairs = do
          (res, edge) <- results' `zip` edges (node curr)
          case res of
            AtOuter -> []
            AtInner res -> res |> fmap (both (dict edge !))
            AtBoundary -> [(symbol edge, snd new_wire)]
              where
              new_wire = new_wires ! symbol2 (curr, edge)

    pairs |> sort |> nub |> filterMaybe (fmap fst .> distinct)

  Just (new_edge, new_wires)

addMorphism ::
  Symbol
  -> Edge e -> Map (Symbol, Symbol) (Symbol, Symbol)
  -> Node e -> Maybe (Node e)
addMorphism src new_edge new_wires bac = do
  src_arr <- bac |> arrow src
  let new_edges = edges (node src_arr) |> (++ [new_edge])
  let res0 = Node new_edges
  fromReachable res0 $ bac |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {node = res}]
    AtBoundary -> [edge {dict = new_dict, node = res0}]
      where
      new_wire = new_wires ! symbol2 (curr, edge)
      new_dict = dict edge |> uncurry Map.insert new_wire

partitionMorphism :: Symbol -> Node e -> Maybe [[(Symbol, Symbol)]]
partitionMorphism tgt bac = do
  guard $ root bac |> locate tgt |> (== Inner)
  Just $
    edges bac
    |> concatMap find3Chains
    |> fmap symbol3
    |> bipartiteEqclass
    |> fmap fst
    |> fmap sort
    |> sort
  where
  find3Chains :: Edge e -> [(Edge e, Arrow e, Edge e)]
  find3Chains arr =
    dict arr
    |> Map.filter (== tgt)
    |> Map.keys
    |> mapMaybe (\sym -> node arr |> parents sym)
    |> concat
    |> fmap (\(b, c) -> (arr, b, c))
  symbol3 :: (Edge e, Arrow e, Edge e) -> ((Symbol, Symbol), (Symbol, Symbol))
  symbol3 (arr1, arr2, arr3) = ((sym1, sym23), (sym12, sym3))
    where
    sym1  = dict arr1                                 ! base
    sym23 =                 dict arr2 `cat` dict arr3 ! base
    sym12 = dict arr1 `cat` dict arr2                 ! base
    sym3  =                                 dict arr3 ! base

splitMorphism :: Ord k => (Symbol, Symbol) -> [k] -> Node e -> Maybe (Node e)
splitMorphism (src, tgt) splittable_keys bac = do
  src_arr <- bac |> arrow src
  splittable_groups <- partitionMorphism tgt (node src_arr)
  guard $ length splittable_groups == length splittable_keys

  let src_syms = node src_arr |> symbols
  let splitted_syms =
        splittable_keys |> label 0 |> fmap (\i -> maximum src_syms * i + tgt)

  let res0 = Node do
        edge <- edges (node src_arr)
        let sym0 = symbol edge
        if sym0 == tgt
        then do
          r' <- splitted_syms
          let split (s, r) = if r == tgt then (s, r') else (s, r)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          [edge {dict = splitted_dict}]
        else do
          let split (s, r) = if r == tgt then (s, r') else (s, r)
                where
                r' =
                  splittable_groups
                  |> findIndex ((sym0, s) `elem`)
                  |> fromJust
                  |> (splitted_syms !!)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          [edge {dict = splitted_dict}]

  fromReachable res0 $ bac |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {node = res}]
    AtBoundary -> [edge {dict = merged_dict, node = res0}]
      where
      merge (s, r)
        | s == tgt  = [(s', r) | s' <- splitted_syms]
        | otherwise = [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

partitionObject :: Node e -> [[Symbol]]
partitionObject bac = links |> bipartiteEqclass |> fmap (snd .> sort) |> sort
  where
  links = do
    arr <- edges bac
    let sym0 = symbol arr
    sym <- dict arr |> Map.elems
    [(sym0, sym)]

splitObject :: Ord k => Symbol -> [k] -> Node e -> Maybe (Node e)
splitObject tgt splittable_keys bac = do
  guard $ root bac |> locate tgt |> (== Inner)
  tgt_arr <- bac |> arrow tgt
  let splittable_groups = partitionObject (node tgt_arr)
  guard $ length splittable_groups == length splittable_keys

  let splitted_groups =
        splittable_keys
        |> sort
        |> nub
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))
  let splitSym syms s =
        splittable_keys |> label 0 |> fmap (\i -> maximum syms * i + s)

  let splitted_res = do
        group <- splitted_groups
        let splitted_edges =
              edges (node tgt_arr) |> filter (\edge -> symbol edge `elem` group)
        [Node splitted_edges]

  fromInner $ bac |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {dict = duplicated_dict, node = res}]
      where
      s_syms = node edge |> symbols
      r_syms = node curr |> symbols
      duplicate (s, r)
        | dict curr ! r == tgt = splitSym s_syms s `zip` splitSym r_syms r
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      let r_syms = node curr |> symbols
      let splitted_syms = splitSym r_syms (symbol edge)
      ((group, sym), res) <- splitted_groups `zip` splitted_syms `zip` splitted_res
      let split (s, r)
            | s == base      = Just (base, sym)
            | s `elem` group = Just (s, r)
            | otherwise      = Nothing
      let splitted_dict =
            dict edge |> Map.toList |> mapMaybe split |> Map.fromList
      [edge {dict = splitted_dict, node = res}]

splitCategory :: Ord k => [k] -> Node e -> Maybe [Node e]
splitCategory splittable_keys bac = do
  let splittable_groups = partitionObject bac
  guard $ length splittable_groups == length splittable_keys

  let splitted_groups =
        splittable_keys
        |> sort
        |> nub
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))

  Just do
    group <- splitted_groups
    let splitted_edges =
          edges bac |> filter (\edge -> symbol edge `elem` group)
    [Node splitted_edges]

mergeMorphisms :: Symbol -> [Symbol] -> Node e -> Maybe (Node e)
mergeMorphisms src tgts bac = do
  src_arr <- bac |> arrow src

  tgt_arrs <- tgts |> traverse \tgt -> node src_arr |> arrow tgt
  guard $ not (null tgt_arrs)
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  guard $
    src /= base
    || (tgt_arrs |> fmap (node .> edges .> fmap dict) |> allSame)
  pars <- bac |> parents src
  pars |> traverse_ \(_, edge) ->
    guard $ tgts |> fmap (dict edge !) |> allSame

  let merge s = if s `elem` tgts then head tgts else s

  let res0 = Node do
        edge <- edges (node src_arr)
        let dict' = dict edge |> Map.toList |> fmap (second merge) |> Map.fromList
        [edge {dict = dict'}]

  fromReachable res0 $ bac |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {node = res}]
    AtBoundary -> [edge {dict = dict', node = res0}]
      where
      dict' = dict edge |> Map.toList |> fmap (first merge) |> Map.fromList

mergeObjects :: [Symbol] -> Node e -> Maybe (Node e)
mergeObjects tgts bac = do
  tgt_pars <- tgts |> traverse \tgt -> do
    pars <- bac |> parents tgt
    Just $
      pars
      |> filter (\(arr, edge) -> symbol edge |> nondecomposable (node arr))
      |> nubOn symbol2

  guard $ not (null tgt_pars)
  guard $ tgt_pars |> fmap length |> allSame
  guard $ transpose tgt_pars |> all (fmap (fst .> symbol) .> allSame)

  let tgt_nodes = tgts |> fmap (`arrow` bac) |> fmap (fromJust .> node)
  let merged_node = mergeCategories tgt_nodes
  let merging_nums = tgt_nodes |> fmap (symbols .> maximum) |> scanl (+) 0

  let merged_dicts = Map.fromList do
        arr_edges <- transpose tgt_pars
        let merged_wire =
              arr_edges |> fmap (snd .> symbol) |> sort |> head |> (base,)
        let merged_dict =
              arr_edges
              |> fmap (snd .> dict .> Map.delete base .> Map.toList)
              |> zip merging_nums
              |> concatMap (\(num, dict) -> dict |> fmap (first (+ num)))
              |> (merged_wire :)
              |> Map.fromList
        key <- arr_edges |> fmap symbol2
        [(key, merged_dict)]

  let placeholder = bac
  let tgt = head tgts
  located_res <- sequence $
    bac |> foldUnder tgt \curr results -> do
      results' <-
        results
        |> traverse sequence
        |> fmap (fmap (fromInner .> fromMaybe (placeholder, [])))

      let collapse_lists1 =
            results' `zip` edges (node curr)
            |> concatMap (\((_, lists), edge) -> lists |> fmap (fmap (dict edge !)))
      let collapse_lists2 =
            edges (node curr)
            |> fmap ((curr,) .> symbol2)
            |> filter (`Map.member` merged_dicts)
            |> sortOn (merged_dicts !)
            |> groupOn (merged_dicts !)
            |> fmap (fmap snd)
      let collapse_lists =
            (collapse_lists1 ++ collapse_lists2) |> fmap sort |> sort |> nub
      guard $ collapse_lists |> concat |> distinct

      let collapsed_edges = do
            ((res_node, collapse_lists'), edge) <- results' `zip` edges (node curr)

            let is_tgt = symbol (curr `join` edge) `elem` tgts
            let collapsed_node = if is_tgt then merged_node else res_node
            let collapsed_dict = case symbol2 (curr, edge) `Map.lookup` merged_dicts of
                  Just dict -> dict
                  Nothing | not is_tgt ->
                    collapse_lists' |> concatMap tail |> foldr Map.delete (dict edge)
                  _ ->
                    edges (node curr)
                    |> findIndex (locate (symbol edge) .> (== Inner))
                    |> fromJust
                    |> (collapsed_edges !!)
                    |> (\edge -> Node [edge])
                    |> arrow (symbol edge)
                    |> fromJust
                    |> dict

            [edge {dict = collapsed_dict, node = collapsed_node}]

      Just (Node collapsed_edges, collapse_lists)

  fromReachable bac $ fmap fst located_res

mergeCategories :: [Node e] -> Node e
mergeCategories bacs = Node {edges = merged_edges}
  where
  nums = bacs |> fmap (symbols .> maximum) |> scanl (+) 0
  merged_edges = do
    (num, bac) <- zip nums bacs
    edge <- edges bac
    let dict' = dict edge |> fmap (+ num)
    [edge {dict = dict'}]

trimObject :: Symbol -> Node e -> Maybe (Node e)
trimObject tgt bac = do
  guard $ root bac |> locate tgt |> (== Inner)
  tgt_arr <- bac |> arrow tgt

  fromReachable (node tgt_arr) $ bac |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> [edge]
    AtBoundary -> do
      subedge <- edges (node edge)
      let concated_dict = dict edge `cat` dict subedge
      [subedge {dict = concated_dict}]
    AtInner res -> [edge {dict = filtered_dict, node = res}]
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

insertMorphism ::
  (Symbol, Maybe Symbol)
  -> (e, e)
  -> Node e -> Maybe (Node e)
insertMorphism (src, tgt) (val1, val2) bac = do
  src_arr <- bac |> arrow src
  let new_sym = node src_arr |> symbols |> maximum |> (+ 1)
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- node src_arr |> arrow tgt
      let new_outdict = node tgt_arr |> symbols |> fmap (\s -> (s, s + 1)) |> Map.fromList
      let new_outedge = Arrow' {dict = new_outdict, node = node tgt_arr, value = val2}
      let new_node = Node {edges = [new_outedge]}
      let new_indict = dict tgt_arr |> Map.mapKeys (+ 1) |> Map.insert base new_sym
      Just $ Arrow' {dict = new_indict, node = new_node, value = val1}
    Nothing ->
      Just $ Arrow' {dict = Map.singleton base new_sym, node = empty, value = val1}

  let res0 = Node $ edges (node src_arr) ++ [new_inedge]

  fromReachable res0 $ bac |> modifyUnder src \(curr, edge) res ->
    case fromReachable res0 res of
      Nothing -> [edge]
      Just res -> [edge {dict = dict', node = res}]
        where
        newSym syms = (+) (maximum syms + 1)
        s_syms = node curr |> symbols
        r_syms = node edge |> symbols
        dict' =
              dict edge
              |> Map.toList
              |> concatMap (\(s, r) ->
                if dict curr ! r == src
                then [(s, r), (newSym s_syms s, newSym r_syms r)]
                else [(s, r)])
              |> Map.fromList

expandMergingSymbols :: Node e -> [[Symbol]] -> Maybe [[Symbol]]
expandMergingSymbols bac =
  traverse (traverse (`arrow` bac))
  .> fmap (
    zip [0 :: Integer ..]
    .> concatMap sequence
    .> fmap (fmap (dict .> Map.toList))
    .> concatMap sequence
    .> fmap (\(a, (b, c)) -> ((a, b), c))
    .> bipartiteEqclass
    .> fmap snd
    .> fmap sort
    .> sort
  )

mergeMorphismsAggressively :: Symbol -> [[Symbol]] -> Node e -> Maybe (Node e)
mergeMorphismsAggressively src tgts bac = do
  src_arr <- bac |> arrow src

  tgt_arrs <- tgts |> traverse (traverse (`arrow` node src_arr))
  guard $ tgt_arrs |> all (fmap node .> fmap root .> allSameBy sameStruct)

  let mergeSymbol tgts' s = tgts' |> filter (elem s) |> (++ [[s]]) |> head |> head

  merging_lists <- expandMergingSymbols (node src_arr) tgts
  let merged_node = Node do
        edge <- edges (node src_arr)
        let merged_dict = dict edge |> fmap (mergeSymbol merging_lists)
        [edge {dict = merged_dict}]
  let res0 = (merged_node, merging_lists)
  let merging_lists_of = fromReachable res0 .> fmap snd .> fromMaybe []

  located_res <- sequence $
    bac |> foldUnder src \curr results -> do
      results' <- traverse sequence results
      merging_lists <-
        results'
        |> concatMap merging_lists_of
        |> zip (node curr |> edges |> fmap dict)
        |> fmap (sequence .> fmap (uncurry (!)))
        |> expandMergingSymbols (node curr)
      let merged_node = Node do
            (res, edge) <- results' `zip` edges (node curr)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol merging_lists)
                  |> Map.mapKeys (mergeSymbol (merging_lists_of res))
            case fromReachable res0 res of
              Nothing -> [edge {dict = merged_dict}]
              Just (res, _) -> [edge {dict = merged_dict, node = res}]
      Just (merged_node, merging_lists)

  fromReachable merged_node $ fmap fst located_res

