{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module BAC.Algorithm where

import Control.Monad (guard)
import qualified Control.Monad as Monad
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (for_)
import Data.List (delete, elemIndices, findIndex, nub, nubBy, sort, sortOn, transpose)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, fromJust)
import Data.Traversable (for)

import Utils.Utils ((|>), (.>), both, nubOn, groupOn)
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
  new_edge = Arrow {dict = new_dict, node = new_node, value = val}

removeMorphism :: (Symbol, Symbol) -> Node e -> Maybe (Node e)
removeMorphism (src, tgt) bac = do
  src_arr <- walk src (root bac)
  for_ (edges (node src_arr)) $ \edge -> do
    guard $ symbolize edge == tgt || tgt `notElem` dict edge

  Monad.join $ toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> do
      let filtered_edges =
            edges (node curr) |> filter (\edge -> symbolize edge /= tgt)
      let bac = node curr `withEdges` filtered_edges
      guard $ symbols bac == (symbols (node curr) |> delete tgt)
      Just bac
    InnerArg curr results -> do
      results' <- traverse sequence results
      let bac = node curr `withEdges` do
            (res, edge) <- results' `zip` edges (node curr)
            case res of
              OuterRes -> [edge]
              InnerRes res -> [edge `withNode` res]
              BoundaryRes res -> [edge `withDict` filtered_dict `withNode` res]
                where
                filtered_dict = dict edge |> Map.delete tgt
      guard $ symbols bac == symbols (node curr)
      Just bac

removeObject :: Symbol -> Node e -> Maybe (Node e)
removeObject tgt bac = do
  guard $ locate tgt (root bac) == Inner
  tgt_arr <- walk tgt (root bac)
  guard $ edges (node  tgt_arr) |> null

  toMaybe $ forUnder tgt bac $ \case
    BoundaryArg curr -> node curr
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        BoundaryRes _ -> []
        InnerRes res -> [edge `withDict` filtered_dict `withNode` res]
          where
          filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

prepareForAddingMorphism
  :: Symbol -> Symbol
  -> [(Symbol, Symbol)] -> [(Symbol, Symbol)]
  -> e
  -> Node e -> Maybe (Edge e, Map (Symbol, Symbol) (Symbol, Symbol))
prepareForAddingMorphism src tgt src_alts tgt_alts val bac = do
  src_arr <- walk src (root bac)
  tgt_arr <- walk tgt (root bac)
  guard $ locate src tgt_arr == Outer

  let new_sym = node src_arr |> symbols |> maximum |> (+ 1)

  src_inedges <- parents src bac
  tgt_outedges <- children tgt bac
  src_outedges' <- traverse (`walk2` root bac) src_alts
  tgt_inedges' <- traverse (`walk2` root bac) tgt_alts

  guard $ length src_inedges == length tgt_inedges'
  guard $ length tgt_outedges == length src_outedges'

  for_ (src_outedges' `zip` tgt_outedges) $ \((arr1', edge1'), (arr1, edge1)) -> do
    guard $ dict arr1 == dict tgt_arr
    guard $ dict arr1' == dict src_arr
    guard $ dict arr1' `cat` dict edge1' == dict arr1 `cat` dict edge1
  for_ (src_inedges `zip` tgt_inedges') $ \((arr2, edge2), (arr2', edge2')) -> do
    guard $ dict arr2' == dict arr2
    guard $ dict arr2 `cat` dict edge2 == dict tgt_arr
    guard $ dict arr2' `cat` dict edge2' == dict tgt_arr
  for_ (src_outedges' `zip` tgt_outedges) $ \((arr1', edge1'), (arr1, edge1)) -> do
    for_ (src_inedges `zip` tgt_inedges') $ \((arr2, edge2), (arr2', edge2')) -> do
      guard $ dict edge2 `cat` dict edge1' == dict edge2' `cat` dict edge1

  new_dict <-
    tgt_outedges
    |> fmap (second asArrow)
    |> (`zip` src_outedges')
    |> concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
    |> sort
    |> nub
    |> groupOn fst
    |> traverse (\case
      [wire] -> Just wire
      _ -> Nothing)
    |> fmap ((base, new_sym) :)
    |> fmap Map.fromList
  let new_edge = Arrow {dict = new_dict, node = node tgt_arr, value = val}

  let new_wires =
        src_inedges
        |> fmap (second asArrow)
        |> (`zip` tgt_inedges')
        |> fmap (both symbolize2)
        |> fmap (second $ snd .> (new_sym,))
        |> Map.fromList

  sequence_ $ forUnder src bac $ \case
    BoundaryArg curr -> Just []
    InnerArg curr results -> do
      results' <- traverse sequence results
      let pairs = do
            (res, edge) <- results' `zip` edges (node curr)
            case res of
              OuterRes -> []
              InnerRes res -> res |> fmap (both (dict edge !))
              BoundaryRes _ -> [(symbolize edge, snd new_wire)]
                where
                new_wire = new_wires ! symbolize2 (curr, edge)

      pairs
        |> sort
        |> nub
        |> groupOn fst
        |> traverse (\case
          [pair] -> Just pair
          _ -> Nothing)

  Just (new_edge, new_wires)

addMorphism
  :: Symbol
  -> Edge e -> Map (Symbol, Symbol) (Symbol, Symbol)
  -> Node e -> Maybe (Node e)
addMorphism src new_edge new_wires bac =
  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` new_edges
      where
      new_edges = edges (node curr) |> (new_edge :)
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withDict` new_dict `withNode` res]
          where
          new_wire = new_wires ! symbolize2 (curr, edge)
          new_dict = dict edge |> uncurry Map.insert new_wire

partitionMorphism :: Symbol -> Node e -> Maybe [[(Symbol, Symbol)]]
partitionMorphism tgt bac = do
  guard $ locate tgt (root bac) == Inner
  Just $
    edges bac
    |> concatMap find3Chains -- list of 3-chains
    |> fmap symbolize3 -- list of links between min and max objects
    |> bipartiteEqclass
    |> fmap fst
    |> fmap sort
    |> sort
  where
  find3Chains :: Edge e -> [(Edge e, Arrow () e, Edge e)]
  find3Chains arr =
    dict arr
    |> Map.filter (== tgt)
    |> Map.keys
    |> mapMaybe (\sym -> parents sym (node arr))
    |> concat
    |> fmap (\(b,c) -> (arr,b,c))
  symbolize3 :: (Edge e, Arrow () e, Edge e) -> ((Symbol, Symbol), (Symbol, Symbol))
  symbolize3 (arr1, arr2, arr3) = ((sym1, sym23), (sym12, sym3))
    where
    sym1  = dict arr1                                 ! base
    sym23 =                 dict arr2 `cat` dict arr3 ! base
    sym12 = dict arr1 `cat` dict arr2                 ! base
    sym3  =                                 dict arr3 ! base

splitMorphism :: Ord k => (Symbol, Symbol) -> [k] -> Node e -> Maybe (Node e)
splitMorphism (src, tgt) splittable_keys bac = do
  src_arr <- walk src (root bac)
  splittable_groups <- partitionMorphism tgt (node src_arr)
  guard $ length splittable_groups == length splittable_keys

  let src_syms = node src_arr |> symbols
  let splitted_syms =
        splittable_keys
        |> sort
        |> nub
        |> (`zip` [maximum src_syms * i + tgt | i <- [0..]])
        |> Map.fromList
        |> (\new_syms -> splittable_keys |> fmap (new_syms !))

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` do
      edge <- edges (node curr)
      let sym0 = symbolize edge
      if sym0 == tgt
      then do
        r' <- splitted_syms
        let split (s, r) = if r == tgt then (s, r') else (s, r)
        let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
        [edge `withDict` splitted_dict]
      else do
        let split (s, r) = if r == tgt then (s, r') else (s, r)
              where
              r' =
                splittable_groups
                |> findIndex ((sym0, s) `elem`)
                |> fromJust
                |> (splitted_syms !!)
        let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
        [edge `withDict` splitted_dict]
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withDict` merged_dict `withNode` res]
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
    let sym0 = symbolize arr
    sym <- dict arr |> Map.elems
    [(sym0, sym)]

splitObject :: Ord k => Symbol -> [k] -> Node e -> Maybe (Node e)
splitObject tgt splittable_keys bac = do
  guard $ locate tgt (root bac) == Inner
  tgt_arr <- walk tgt (root bac)
  let splittable_groups = partitionObject (node tgt_arr)
  guard $ length splittable_groups == length splittable_keys

  let splitted_groups =
        splittable_keys
        |> sort
        |> nub
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))
  let splitSym syms s =
        splittable_keys
        |> sort
        |> nub
        |> (`zip` [maximum syms * i + s | i <- [0..]])
        |> Map.fromList
        |> (\new_syms -> splittable_keys |> fmap (new_syms !))

  let f_boundary curr = do
        group <- splitted_groups
        let splitted_edges =
              edges (node curr) |> filter (\edge -> symbolize edge `elem` group)
        [node curr `withEdges` splitted_edges]

  let f_inner curr results = node curr `withEdges` do
        (res, edge) <- results `zip` edges (node curr)
        let s_syms = node edge |> symbols
        let r_syms = node curr |> symbols
        case res of
          OuterRes' -> [edge]
          InnerRes' res -> [edge `withDict` duplicated_dict `withNode` res]
            where
            duplicate (s, r)
              | dict curr ! r == tgt = splitSym s_syms s `zip` splitSym r_syms r
              | otherwise            = [(s, r)]
            duplicated_dict =
              dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
          BoundaryRes' splitted_res -> do
            let splitted_syms = splitSym r_syms (symbolize edge)
            ((group, sym), res) <- splitted_groups `zip` splitted_syms `zip` splitted_res
            let split (s, r)
                  | s == base      = Just (base, sym)
                  | s `elem` group = Just (s, r)
                  | otherwise      = Nothing
            let splitted_dict =
                  dict edge |> Map.toList |> mapMaybe split |> Map.fromList
            [edge `withDict` splitted_dict `withNode` res]

  case foldUnder' tgt f_inner f_boundary bac of
    InnerRes' res -> Just res
    _ -> Nothing

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

  Just $ do
    group <- splitted_groups
    let splitted_edges =
          edges bac |> filter (\edge -> symbolize edge `elem` group)
    [bac `withEdges` splitted_edges]

mergeMorphisms :: Symbol -> [Symbol] -> Node e -> Maybe (Node e)
mergeMorphisms src tgts bac = do
  src_arr <- walk src (root bac)

  tgt_arrs <- for tgts $ \tgt -> walk tgt (root (node src_arr))
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> nub |> length |> (== 1)
  guard $
    src /= base
    || (tgt_arrs |> fmap (node .> edges .> fmap dict) |> nub |> length |> (== 1))
  pars <- parents src bac
  for_ pars $ \(_, edge) -> do
    guard $ tgts |> fmap (dict edge !) |> nub |> length |> (== 1)

  let merge s = if s `elem` tgts then head tgts else s

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` do
      edge <- edges (node curr)
      let dict' = dict edge |> Map.toList |> fmap (second merge) |> Map.fromList
      [edge `withDict` dict']
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withDict` dict' `withNode` res]
          where
          dict' = dict edge |> Map.toList |> fmap (first merge) |> Map.fromList

mergeObjects :: [Symbol] -> Node e -> Maybe (Node e)
mergeObjects tgts bac = do
  tgt_pars <- for tgts $ \tgt -> do
    pars <- parents tgt bac
    Just $
      pars
      |> filter (\(arr, edge) -> isNondecomposable (node arr) (symbolize edge))
      |> nubOn symbolize2

  guard $ tgt_pars |> fmap length |> nub |> length |> (== 1)
  guard $ transpose tgt_pars |> all (fmap (fst .> symbolize) .> nub .> length .> (== 1))

  let tgt_nodes = tgts |> fmap (`walk` root bac) |> fmap (fromJust .> node)
  let merged_node = mergeCategories tgt_nodes
  let merging_nums = tgt_nodes |> fmap (symbols .> maximum) |> scanl (+) 0

  let merged_dicts = Map.fromList $ do
        arr_edges <- transpose tgt_pars
        let merged_wire =
              arr_edges |> fmap (snd .> symbolize) |> sort |> head |> (base,)
        let merged_dict =
              arr_edges
              |> fmap (snd .> dict .> Map.delete base .> Map.toList)
              |> zip merging_nums
              |> concatMap (\(num, dict) -> dict |> fmap (first (+ num)))
              |> (merged_wire :)
              |> Map.fromList
        key <- arr_edges |> fmap symbolize2
        [(key, merged_dict)]

  let tgt = head tgts
  fmap fst $ flip fold bac $ \curr results -> case locate tgt curr of
    Outer -> Just (node curr, [])
    Boundary -> Just (node curr, [])
    Inner -> do
      results' <- sequence results

      let collapse_lists1 =
            results' `zip` edges (node curr)
            |> concatMap (\((_, lists), edge) -> lists |> fmap (fmap (dict edge !)))
      let collapse_lists2 =
            edges (node curr)
            |> fmap ((curr,) .> symbolize2)
            |> filter (`Map.member` merged_dicts)
            |> sortOn (merged_dicts !)
            |> groupOn (merged_dicts !)
            |> fmap (fmap snd)
      let collapse_lists =
            (collapse_lists1 ++ collapse_lists2) |> fmap sort |> sort |> nub
      guard $ (collapse_lists |> concat |> nub) == (collapse_lists |> concat)

      let collapsed_edges = do
            ((res_node, collapse_lists'), edge) <- results' `zip` edges (node curr)

            let is_tgt = symbolize (join curr edge) `elem` tgts
            let collapsed_node = if is_tgt then merged_node else res_node
            let collapsed_dict = case symbolize2 (curr, edge) `Map.lookup` merged_dicts of
                  Just dict -> dict
                  Nothing | not is_tgt ->
                    collapse_lists' |> concatMap tail |> foldr Map.delete (dict edge)
                  _ ->
                    edges (node curr)
                    |> findIndex (locate (symbolize edge) .> (== Inner))
                    |> fromJust
                    |> (collapsed_edges !!)
                    |> walk (symbolize edge)
                    |> fromJust
                    |> dict

            [edge `withDict` collapsed_dict `withNode` collapsed_node]

      Just (node curr `withEdges` collapsed_edges, collapse_lists)

mergeCategories :: [Node e] -> Node e
mergeCategories bacs = Node {edges = merged_edges}
  where
  nums = bacs |> fmap (symbols .> maximum) |> scanl (+) 0
  merged_edges = do
    (num, bac) <- zip nums bacs
    edge <- edges bac
    let dict' = dict edge |> fmap (+ num)
    [edge `withDict` dict']

trimObject :: Symbol -> Node e -> Maybe (Node e)
trimObject tgt bac = do
  guard $ locate tgt (root bac) == Inner

  toMaybe $ forUnder tgt bac $ \case
    BoundaryArg curr -> node curr
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        BoundaryRes _ -> do
          subedge <- edges (node edge)
          let concated_dict = dict edge `cat` dict subedge
          [subedge `withDict` concated_dict]
        InnerRes res -> [edge `withDict` filtered_dict `withNode` res]
          where
          filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

insertMorphism
  :: (Symbol, Maybe Symbol)
  -> (e, e)
  -> Node e -> Maybe (Node e)
insertMorphism (src, tgt) (val1, val2) bac = do
  src_arr <- src `walk` root bac
  let new_sym = node src_arr |> symbols |> maximum |> (+ 1)
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- root (node src_arr) |> walk tgt
      let new_outdict = node tgt_arr |> symbols |> fmap (\s -> (s, s + 1)) |> Map.fromList
      let new_outedge = Arrow {dict = new_outdict, node = node tgt_arr, value = val2}
      let new_node = Node {edges = [new_outedge]}
      let new_indict = dict tgt_arr |> Map.mapKeys (+ 1) |> Map.insert base new_sym
      Just $ Arrow {dict = new_indict, node = new_node, value = val1}
    Nothing ->
      Just $ Arrow {dict = Map.singleton base new_sym, node = empty, value = val1}

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` (edges (node curr) ++ [new_inedge])
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      let s_syms = node curr |> symbols
      let r_syms = node edge |> symbols
      let dict' =
            dict edge
            |> Map.toList
            |> concatMap (\(s, r) ->
              if dict curr ! r == src
              then [(s, r), (newSym s_syms s, newSym r_syms r)]
              else [(s, r)])
            |> Map.fromList
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withDict` dict' `withNode` res]
        BoundaryRes res -> [edge `withDict` dict' `withNode` res]
      where
      newSym syms = (+) (maximum syms + 1)

expandMergingSymbols :: Node e -> [[Symbol]] -> Maybe [[Symbol]]
expandMergingSymbols bac =
  traverse (traverse (`walk` root bac))
  .> fmap (
    zip ([0..] :: [Integer])
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
  src_arr <- walk src (root bac)

  tgt_arrs <- traverse (traverse (`walk` root (node src_arr))) tgts
  guard $
    tgt_arrs |> all (fmap node .> fmap root .> nubBy sameStruct .> length .> (<= 1))

  let mergeSymbol tgts' s = tgts' |> filter (elem s) |> (++ [[s]]) |> head |> head

  fmap fst $ Monad.join $ toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> do
      merging_lists <- expandMergingSymbols (node curr) tgts
      let merged_node = node curr `withEdges` do
            edge <- edges (node curr)
            let merged_dict = dict edge |> fmap (mergeSymbol merging_lists)
            [edge `withDict` merged_dict]
      Just (merged_node, merging_lists)
    InnerArg curr results -> do
      results' <- traverse sequence results
      merging_lists <-
        results'
        |> mapMaybe toMaybe
        |> concatMap snd
        |> zip (node curr |> edges |> fmap dict)
        |> fmap (sequence .> fmap (uncurry (!)))
        |> expandMergingSymbols (node curr)
      let merged_node = node curr `withEdges` do
            (res, edge) <- results' `zip` edges (node curr)
            let merging_lists' = res |> toMaybe |> fmap snd |> fromMaybe []
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol merging_lists)
                  |> Map.mapKeys (mergeSymbol merging_lists')
            case res of
              OuterRes -> [edge `withDict` merged_dict]
              InnerRes (res, _) -> [edge `withDict` merged_dict `withNode` res]
              BoundaryRes (res, _) -> [edge `withDict` merged_dict `withNode` res]
      Just (merged_node, merging_lists)

