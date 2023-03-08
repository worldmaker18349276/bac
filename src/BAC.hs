{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module BAC where

import Control.Monad (guard)
import qualified Control.Monad as Monad
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Foldable (for_)
import Data.Function ((&))
import Data.List (delete, elemIndices, findIndex, groupBy, nub, nubBy, sort, sortOn, transpose)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, fromJust, isJust, listToMaybe)
import Data.Traversable (for)
import Data.Tuple (swap)
import DisjointSet (bipartiteEqclass)
import Memoize (unsafeMemoizeWithKey)
import qualified DAG
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT, MaybeT))
import Control.Monad.Identity (Identity (runIdentity))

-- flow

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

both :: (a -> b) -> (a, a) -> (b, b)
both f (a, a') = (f a, f a')

nubOn :: Eq b => (a -> b) -> [a] -> [a]
nubOn f = nubBy (\a a' -> f a == f a')

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy (\a a' -> f a == f a')

-- basic types

data Arrow v e n = Arrow {dict :: Dict, node :: Node e n, evalue :: v}
  deriving (Eq, Ord, Show)

type Edge e n = Arrow e e n

data Node e n = Node {edges :: [Edge e n], nvalue :: n} deriving (Eq, Ord, Show)

type Dict = Map Symbol Symbol

newtype Symbol = Symbol [Integer] deriving (Eq, Ord, Show)

base :: Symbol
base = Symbol []

symbols :: Node e n -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> sort .> nub .> (base :)

isValidSymbols :: [Symbol] -> Bool
isValidSymbols syms = head == [base] && all validate (tail `zip` drop 1 tail)
  where
  sorted_syms = sort syms
  head = take 1 sorted_syms
  tail = drop 1 sorted_syms
  validate (Symbol (a:r), Symbol (b:s)) = a /= b || validate (Symbol r, Symbol s)
  validate _ = False

relabel :: ([Integer] -> [Integer]) -> (Symbol -> Symbol)
relabel f (Symbol a) = Symbol (f a)

makeNewSymbol :: [Symbol] -> Symbol
makeNewSymbol =
  concatMap (\(Symbol nums) -> nums |> take 1)
  .> fmap (+ 1)
  .> (0 :)
  .> maximum
  .> (: [])
  .> Symbol

splitSymbol :: Symbol -> [Integer] -> [Symbol]
splitSymbol s = fmap (\num -> relabel (++ [num]) s)

mergeSymbols :: Map Integer [Symbol] -> [Symbol]
mergeSymbols = Map.toList .> concatMap sequence .> fmap (\(num, sym) -> relabel (num :) sym)

--   (isValidSymbols syms && sym /= base) -> isValidSymbols (delete sym syms)
--   isValidSymbols syms -> isValidSymbols (syms ++ [makeNewSymbol syms])
--   (isValidSymbols syms && sym /= base && sym `elem` syms)
--     -> isValidSymbols (delete sym syms ++ splitSymbol sym nums)
--   all isValidSymbols syms -> isValidSymbols (base : mergeSymbols syms)

cat :: Dict -> Dict -> Dict
cat = fmap . (!)

withDict :: Arrow v e n -> Dict -> Arrow v e n
withDict edge dict = edge {dict = dict}

withNode :: Arrow v e n -> Node o m -> Arrow v o m
withNode edge node = edge {node = node}

withEdges :: Node e n -> [Edge o n] -> Node o n
withEdges bac edges = bac {edges = edges}

asArrow :: Arrow v e n -> Arrow () e n
asArrow edge = edge {evalue = ()}

-- explore methods

data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

root :: Node e n -> Arrow () e n
root bac = Arrow {dict = id_dict, node = bac, evalue = ()}
  where
  id_dict = bac |> symbols |> fmap (\a -> (a, a)) |> Map.fromList

join :: Arrow v e n -> Arrow w e n -> Arrow () e n
join arr1 arr2 = asArrow $ arr2 `withDict` (dict arr1 `cat` dict arr2)

next :: Arrow v e n -> [Arrow () e n]
next arr = edges (node arr) |> fmap (join arr)

locate :: Symbol -> Arrow v e n -> Location
locate sym arr
  | symbolize arr == sym = Boundary
  | sym `elem` dict arr  = Inner
  | otherwise            = Outer

walk :: Symbol -> Arrow v e n -> Maybe (Arrow () e n)
walk sym arr = case locate sym arr of
  Outer    -> Nothing
  Boundary -> Just (asArrow arr)
  Inner    -> Just $ arr |> next |> mapMaybe (walk sym) |> head

walk2 :: (Symbol, Symbol) -> Arrow v e n -> Maybe (Arrow () e n, Arrow () e n)
walk2 (src, tgt) arr = do
  src_arr <- walk src arr
  tgt_subarr <- walk tgt (root (node src_arr))
  Just (src_arr, tgt_subarr)

symbolize :: Arrow v e n -> Symbol
symbolize = dict .> (! base)

symbolize2 :: (Arrow v e n, Arrow w e n) -> (Symbol, Symbol)
symbolize2 = symbolize `bimap` symbolize

walkAll :: Symbol -> Arrow v e n -> [Arrow () e n]
walkAll sym arr = case locate sym arr of
  Outer    -> []
  Boundary -> [asArrow arr]
  Inner    -> arr |> next |> concatMap (walkAll sym)

isNondecomposable :: Node e n -> Symbol -> Bool
isNondecomposable bac sym =
  locate sym (root bac) == Inner
  && all (locate sym .> (/= Inner)) (edges bac)

children :: Symbol -> Node e n -> Maybe [(Arrow () e n, Edge e n)]
children tgt bac = do
  tgt_arr <- walk tgt (root bac)
  Just $ edges (node tgt_arr) |> fmap (tgt_arr,) |> sortOn symbolize2

parents :: Symbol -> Node e n -> Maybe [(Arrow () e n, Edge e n)]
parents tgt bac = do
  arrs <- findUnder tgt is_parent bac
  Just $
    arrs
    |> fmap (node .> edges)
    |> zip arrs
    |> concatMap sequence
    |> filter (uncurry join .> locate tgt .> (== Boundary))
    |> sortOn symbolize2
  where
  is_parent _ = next .> any (locate tgt .> (== Boundary))

sameStruct :: Arrow v e n -> Arrow w o m -> Bool
sameStruct arr1 arr2 =
  dict arr1 == dict arr2
  && length (edges (node arr1)) == length (edges (node arr2))
  && (edges (node arr1) `zip` edges (node arr2) |> all (uncurry sameStruct))

validate :: Node e n -> Bool
validate bac =
  validateSymbols
  && validateChildren
  && validateDicts
  && validateSup
  where
  validateSymbols = symbols bac |> isValidSymbols
  validateChildren = edges bac |> fmap node |> all validate
  validateDicts =
    edges bac
    |> all (\edge -> Map.keys (dict edge) == symbols (node edge))
  validateSup =
    edges bac
    |> fmap node
    |> fmap (\node -> symbols node |> fmap (`walk` root node) |> fmap fromJust)
    |> zip (edges bac)
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (root bac :)
    |> sortOn symbolize
    |> groupOn symbolize
    |> all (nubBy sameStruct .> length .> (== 1))

-- fold methods

fold :: (Arrow () e n -> [r] -> r) -> (Node e n -> r)
fold f = root .> fold'
  where
  fold' = memoize $ \arr -> f arr (arr |> next |> fmap fold')
  memoize = unsafeMemoizeWithKey symbolize

data FoldUnderResult r = InnerRes r | BoundaryRes r | OuterRes
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
data FoldUnderArgument e n r =
  InnerArg (Arrow () e n) [FoldUnderResult r] | BoundaryArg (Arrow () e n)
  deriving (Functor, Foldable, Traversable)

toMaybe :: FoldUnderResult r -> Maybe r
toMaybe (InnerRes r) = Just r
toMaybe (BoundaryRes r) = Just r
toMaybe OuterRes = Nothing

foldUnder :: Symbol -> (FoldUnderArgument e n r -> r) -> (Node e n -> FoldUnderResult r)
foldUnder sym f = fold f'
  where
  f' arr results = case locate sym arr of
    Outer    -> OuterRes
    Boundary -> BoundaryRes $ f $ BoundaryArg arr
    Inner    -> InnerRes    $ f $ InnerArg    arr results

forUnder :: Symbol -> Node e n -> (FoldUnderArgument e n r -> r) -> FoldUnderResult r
forUnder sym = flip (foldUnder sym)

data FoldUnderResult' r s = InnerRes' r | BoundaryRes' s | OuterRes'

foldUnder'
  :: Symbol
  -> (Arrow () e n -> [FoldUnderResult' r s] -> r)
  -> (Arrow () e n                           -> s)
  -> (Node e n -> FoldUnderResult' r s)
foldUnder' sym f_inner f_boundary = fold f'
  where
  f' arr results = case locate sym arr of
    Outer    -> OuterRes'
    Boundary -> BoundaryRes' $ f_boundary arr
    Inner    -> InnerRes'    $ f_inner    arr results

map :: (Arrow () e n -> m) -> ((Arrow () e n, Edge e n) -> o) -> (Node e n -> Node o m)
map f g = fold go
  where
  go arr results = Node {edges = edges', nvalue = f arr}
    where
    edges' =
      edges (node arr)
      |> fmap (\edge -> edge {evalue = g (arr, edge)})
      |> (`zip` results)
      |> fmap (uncurry withNode)

mapUnder
  :: Symbol
  -> (Location -> Arrow () e n -> n)
  -> (Location -> (Arrow () e n, Edge e n) -> e)
  -> (Node e n -> Maybe (Node e n))
mapUnder sym f g = foldUnder sym go .> toMaybe
  where
  go = \case
    BoundaryArg curr -> Node {edges = edges (node curr), nvalue = f Boundary curr}
    InnerArg curr results -> Node {edges = edges', nvalue = f Inner curr}
      where
      edges' = do
        (edge, res) <- edges (node curr) `zip` results
        case res of
          BoundaryRes res -> [edge {evalue = g Boundary (curr, edge)} `withNode` res]
          InnerRes res -> [edge {evalue = g Inner (curr, edge)} `withNode` res]
          OuterRes -> [edge]

find :: (Arrow () e n -> Bool) -> (Node e n -> [Arrow () e n])
find f = fold go .> Map.elems
  where
  go arr results =
    if f arr
    then Map.unions results |> Map.insert (symbolize arr) arr
    else Map.unions results

findUnder
  :: Symbol -> (Location -> Arrow () e n -> Bool) -> (Node e n -> Maybe [Arrow () e n])
findUnder sym f = foldUnder sym go .> toMaybe .> fmap Map.elems
  where
  go arg =
    if f loc arr
    then Map.unions results |> Map.insert (symbolize arr) arr
    else Map.unions results
    where
    (arr, loc, results) = case arg of
      BoundaryArg arr -> (arr, Boundary, [])
      InnerArg arr results -> (arr, Inner, results |> mapMaybe toMaybe)

filterEdges :: Symbol -> (Int -> Edge e n -> Bool) -> Node e n -> Maybe (Node e n)
filterEdges src pred bac = do
  src_arr <- walk src (root bac)
  let src_edges = edges (node src_arr)
  let src_edges' = [0..] `zip` src_edges |> filter (uncurry pred) |> fmap snd
  let nd_syms = fmap symbolize .> filter (isNondecomposable (node src_arr)) .> sort .> nub
  guard $ nd_syms src_edges == nd_syms src_edges'

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` src_edges'
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withNode` res]

addEdge :: (Symbol, Symbol) -> e -> Node e n -> Maybe (Node e n)
addEdge (src, tgt) eval bac = do
  guard $ tgt /= base
  (_, tgt_arr) <- walk2 (src, tgt) (root bac)
  let relinked_edge = tgt_arr {evalue = eval}
  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` (edges (node curr) ++ [relinked_edge])
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withNode` res]

reorderEdges :: Ord k => Symbol -> (Int -> Edge e n -> k) -> Node e n -> Maybe (Node e n)
reorderEdges src key bac =
  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` sorted_edges
      where
      sorted_edges = edges (node curr) |> zip [0..] |> sortOn (uncurry key) |> fmap snd
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withNode` res]

relabelObject :: Symbol -> Dict -> Node e n -> Maybe (Node e n)
relabelObject tgt mapping bac = do
  tgt_arr <- walk tgt (root bac)
  guard $ isValidSymbols (Map.elems mapping)
  guard $ mapping ! base == base
  guard $ Map.keys mapping == symbols (node tgt_arr)
  toMaybe $ forUnder tgt bac $ \case
    BoundaryArg curr -> node curr `withEdges` do
      edge <- edges (node curr)
      let relabelled_dict = mapping `cat` dict edge
      [edge `withDict` relabelled_dict]
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withDict` relabelled_dict `withNode` res]
          where
          unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
          relabelled_dict = dict edge `cat` unmapping

-- algorithms

empty :: n -> Node e n
empty nval = Node {edges = [], nvalue = nval}

singleton :: (n, e, n) -> Integer -> Node e n
singleton (nval1, eval, nval2) num = Node {edges = [new_edge], nvalue = nval1}
  where
  new_sym = Symbol [num]
  new_dict = Map.singleton base new_sym
  new_node = Node {edges = [], nvalue = nval2}
  new_edge = Arrow {dict = new_dict, node = new_node, evalue = eval}

removeMorphism :: (Symbol, Symbol) -> Node e n -> Maybe (Node e n)
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

removeObject :: Symbol -> Node e n -> Maybe (Node e n)
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
  -> Integer
  -> Node e n -> Maybe (Edge e n, Map (Symbol, Symbol) (Symbol, Symbol))
prepareForAddingMorphism src tgt src_alts tgt_alts eval num bac = do
  src_arr <- walk src (root bac)
  tgt_arr <- walk tgt (root bac)
  guard $ locate src tgt_arr == Outer
  let new_sym = Symbol [num]
  guard $ node src_arr |> symbols |> (new_sym :) |> isValidSymbols

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
  let new_edge = Arrow {dict = new_dict, node = node tgt_arr, evalue = eval}

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
  -> Edge e n -> Map (Symbol, Symbol) (Symbol, Symbol)
  -> Node e n -> Maybe (Node e n)
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

partitionMorphism :: Symbol -> Node e n -> Maybe [[(Symbol, Symbol)]]
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
  find3Chains :: Edge e n -> [(Edge e n, Arrow () e n, Edge e n)]
  find3Chains arr =
    dict arr
    |> Map.filter (== tgt)
    |> Map.keys
    |> mapMaybe (\sym -> parents sym (node arr))
    |> concat
    |> fmap (\(b,c) -> (arr,b,c))
  symbolize3 :: (Edge e n, Arrow () e n, Edge e n) -> ((Symbol, Symbol), (Symbol, Symbol))
  symbolize3 (arr1, arr2, arr3) = ((sym1, sym23), (sym12, sym3))
    where
    sym1  = dict arr1                                 ! base
    sym23 =                 dict arr2 `cat` dict arr3 ! base
    sym12 = dict arr1 `cat` dict arr2                 ! base
    sym3  =                                 dict arr3 ! base

splitMorphism :: (Symbol, Symbol) -> [Integer] -> Node e n -> Maybe (Node e n)
splitMorphism (src, tgt) splittable_nums bac = do
  src_arr <- walk src (root bac)
  splittable_groups <- partitionMorphism tgt (node src_arr)
  guard $ length splittable_groups == length splittable_nums

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` do
      edge <- edges (node curr)
      let sym0 = symbolize edge
      if sym0 == tgt
      then do
        r' <- splitSymbol tgt splittable_nums
        let split (s, r) = if r == tgt then (s, r') else (s, r)
        let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
        [edge `withDict` splitted_dict]
      else do
        let split (s, r) = case findIndex ((sym0, s) `elem`) splittable_groups of
              Nothing -> (s, r)
              Just n  -> (s, splitSymbol r splittable_nums !! n)
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
            | s == tgt  = [(s', r) | s' <- splitSymbol tgt splittable_nums]
            | otherwise = [(s, r)]
          merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

partitionObject :: Node e n -> [[Symbol]]
partitionObject bac = links |> bipartiteEqclass |> fmap (snd .> sort) |> sort
  where
  links = do
    arr <- edges bac
    let sym0 = symbolize arr
    sym <- dict arr |> Map.elems
    [(sym0, sym)]

splitObject :: Symbol -> [Integer] -> Node e n -> Maybe (Node e n)
splitObject tgt splittable_nums bac = do
  guard $ locate tgt (root bac) == Inner
  tgt_arr <- walk tgt (root bac)
  let splittable_groups = partitionObject (node tgt_arr)
  guard $ length splittable_groups == length splittable_nums

  let splitted_groups =
        splittable_nums
        |> sort
        |> nub
        |> fmap (`elemIndices` splittable_nums)
        |> fmap (concatMap (splittable_groups !!))
  let splitSym s =
        splittable_nums
        |> sort
        |> nub
        |> splitSymbol s

  let f_boundary curr = do
        group <- splitted_groups
        let splitted_edges =
              edges (node curr) |> filter (\edge -> symbolize edge `elem` group)
        [node curr `withEdges` splitted_edges]

  let f_inner curr results = node curr `withEdges` do
        (res, edge) <- results `zip` edges (node curr)
        case res of
          OuterRes' -> [edge]
          InnerRes' res -> [edge `withDict` duplicated_dict `withNode` res]
            where
            duplicate (s, r)
              | dict curr ! r == tgt = splitSym s `zip` splitSym r
              | otherwise            = [(s, r)]
            duplicated_dict =
              dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
          BoundaryRes' splitted_res -> do
            let splitted_syms = splitSym (symbolize edge)
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

splitCategory :: [Integer] -> Node e n -> Maybe [Node e n]
splitCategory splittable_nums bac = do
  let splittable_groups = partitionObject bac
  guard $ length splittable_groups == length splittable_nums

  let splitted_groups =
        splittable_nums
        |> sort
        |> nub
        |> fmap (`elemIndices` splittable_nums)
        |> fmap (concatMap (splittable_groups !!))

  Just $ do
    group <- splitted_groups
    let splitted_edges =
          edges bac |> filter (\edge -> symbolize edge `elem` group)
    [bac `withEdges` splitted_edges]

mergeMorphisms :: Symbol -> [Symbol] -> Node e n -> Maybe (Node e n)
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

mergeObjects :: Map Integer Symbol -> n -> Node e n -> Maybe (Node e n)
mergeObjects tgts nval bac = do
  tgt_pars <- for tgts $ \tgt -> do
    pars <- parents tgt bac
    Just $
      pars
      |> filter (\(arr, edge) -> isNondecomposable (node arr) (symbolize edge))
      |> nubOn symbolize2

  guard $ tgt_pars |> Map.elems |> fmap length |> nub |> length |> (== 1)
  guard $ tgt_pars
    |> Map.elems
    |> fmap (fmap (fst .> symbolize))
    |> transpose
    |> all (nub .> length .> (== 1))

  tgt_nodes <- tgts |> traverse (`walk` root bac) |> fmap (fmap node)
  let merged_node = mergeCategories nval tgt_nodes

  let merged_dicts = Map.fromList $ do
        arr_edges <- tgt_pars
          |> Map.toList
          |> fmap sequence
          |> transpose
        let merged_wire =
              arr_edges |> fmap (snd .> snd .> symbolize) |> sort |> head |> (base,)
        let merged_dict =
              arr_edges
              |> fmap (second (snd .> dict .> Map.delete base .> Map.toList))
              |> concatMap (\(num, dict) -> dict |> fmap (first (relabel (num :))))
              |> (merged_wire :)
              |> Map.fromList
        key <- arr_edges |> fmap (snd .> symbolize2)
        [(key, merged_dict)]

  let tgt = tgts |> Map.elems |> head
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
      guard $
        (collapse_lists |> concat |> sort |> nub |> length)
        == (collapse_lists |> fmap length |> sum)

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

mergeCategories :: n -> Map Integer (Node e n) -> Node e n
mergeCategories nval bacs = Node {edges = merged_edges, nvalue = nval}
  where
  merged_edges = do
    (num, bac) <- Map.toList bacs
    edge <- edges bac
    let dict' = dict edge |> fmap (relabel (num :))
    [edge `withDict` dict']

trimObject :: Symbol -> Node e n -> Maybe (Node e n)
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
  -> (Integer, Integer)
  -> (e, n, e)
  -> Node e n -> Maybe (Node e n)
insertMorphism (src, tgt) (num1, num2) (eval1, nval, eval2) bac = do
  src_arr <- src `walk` root bac
  let new_sym1 = Symbol [num1]
  guard $ node src_arr |> symbols |> (new_sym1 :) |> isValidSymbols
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- tgt `walk` root (node src_arr)
      let new_sym2 = Symbol [num2]
      guard $ node tgt_arr |> symbols |> (new_sym2 :) |> isValidSymbols
      let new_outdict = node tgt_arr |> root |> dict |> Map.insert base new_sym2
      let new_outedge = Arrow {dict = new_outdict, node = node tgt_arr, evalue = eval2}
      let new_node = Node {edges = [new_outedge], nvalue = nval}
      let new_indict = dict tgt_arr |> Map.insert new_sym2 tgt |> Map.insert base new_sym1
      Just $ Arrow {dict = new_indict, node = new_node, evalue = eval1}
    Nothing ->
      Just $ Arrow {dict = Map.singleton base new_sym1, node = empty nval, evalue = eval1}

  toMaybe $ forUnder src bac $ \case
    BoundaryArg curr -> node curr `withEdges` (edges (node curr) ++ [new_inedge])
    InnerArg curr results -> node curr `withEdges` do
      (res, edge) <- results `zip` edges (node curr)
      let dict' =
            dict edge
            |> Map.toList
            |> concatMap (\(s, s') ->
              if dict curr ! s' == src
              then splitSym s `zip` splitSym s'
              else [(s, s')])
            |> Map.fromList
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withDict` dict' `withNode` res]
        BoundaryRes res -> [edge `withDict` dict' `withNode` res]
      where
      splitSym s = if s /= base then splitSymbol s [num1, num1-1] else [new_sym1, base]

expandMergingSymbols :: Node e n -> [[Symbol]] -> Maybe [[Symbol]]
expandMergingSymbols bac =
  traverse (traverse (`walk` root bac))
  .> fmap (
    zip [0..]
    .> concatMap sequence
    .> fmap (fmap (dict .> Map.toList))
    .> concatMap sequence
    .> fmap (\(a, (b, c)) -> ((a, b), c))
    .> bipartiteEqclass
    .> fmap snd
    .> fmap sort
    .> sort
  )

mergeMorphismsAggressively :: Symbol -> [[Symbol]] -> Node e n -> Maybe (Node e n)
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

type BraiderT e n p m v = DAG.BuilderT (Edge e n) (Node e n) p (MaybeT m) v

knot :: (DAG.Pointer p, Monad m) => n -> [(e, p)] -> [[[Int]]] -> BraiderT e n p m p
knot value children eqclass = do
  table <- DAG.getTable

  let node =
        children
        |> fmap (second ((table !) .> fst))
        |> zip [0..]
        |> fmap (\(num, (eval, subnode)) ->
          subnode
          |> symbols
          |> fmap (\a -> (a, relabel (num :) a))
          |> Map.fromList
          |> \dict -> Arrow {dict = dict, node = subnode, evalue = eval}
        )
        |> \edges -> Node {edges = edges, nvalue = value}

  let maybe_list !!? i = maybe_list >>= (take i .> listToMaybe)
  let pathToPointer indices =
        foldl
        (fmap ((table !) .> snd .> fmap snd) .> (!!?))
        (head indices |> (children |> fmap snd |> Just |> (!!?)))
        (tail indices)

  lift $ MaybeT $ pure $ for_ eqclass $ \rels -> do
    guard $ rels |> all (null .> not)
    ptrs <- rels |> traverse pathToPointer
    guard $ ptrs |> nub |> length |> (<= 1)

  let pathToArrow indices =
        foldl
        (next .> (!!))
        (head indices |> (edges node !!) |> asArrow)
        (tail indices)

  let eqclass' =
        eqclass
        |> fmap (fmap (pathToArrow .> symbolize))
        |> expandMergingSymbols node
        |> fromJust

  let mergeSymbol sym = eqclass' |> filter (elem sym) |> (++ [[sym]]) |> head |> head
  let merged_edges = do
        edge <- edges node
        let merged_dict = dict edge |> fmap mergeSymbol
        let merged_edge = edge {dict = merged_dict}
        [merged_edge]
  let merged_node = node {edges = merged_edges}
  let merged_children = children |> zip (edges merged_node) |> fmap (fmap snd)

  DAG.node merged_node merged_children

braidM
  :: Monad m => (forall p. DAG.Pointer p => BraiderT e n p m p) -> m (Maybe (Node e n))
braidM braiding =
  DAG.buildM braiding |> runMaybeT |> fmap (fmap DAG.value)

braid :: (forall p. DAG.Pointer p => BraiderT e n p Identity p) -> Maybe (Node e n)
braid braiding = runIdentity (braidM braiding)

{-
cone :: Maybe (Node Int String)
cone = braid $ do
  y <- knot "side" [] []
  b <- knot "bottom" [] []
  p <- knot "tip" [(2, y)] []
  c <- knot "circle" [(1, y), (-1, b)] []
  v <- knot "point" [(1, c), (-1, c)]
    [
      [[0,0], [1,0]],
      [[0,1], [1,1]]
    ]
  knot "void" [(1, p), (1, v)]
    [
      [[1,0], [1,1]],
      [[0,0], [1,0,0]]
    ]

torus :: Maybe (Node Int String)
torus = braid $ do
  t <- knot "torus" [] []
  c <- knot "circle" [(1, t), (-1, t)] []
  c' <- knot "circle'" [(1, t), (-1, t)] []
  p <- knot "intersected point" [(1, c), (1, c'), (-1, c), (-1, c')]
    [
      [[0,1], [1,0]],
      [[1,1], [2,1]],
      [[2,0], [3,1]],
      [[3,0], [0,0]]
    ]
  knot "void" [(1, p)]
    [
      [[0,0], [0,2]],
      [[0,1], [0,3]]
      -- induced: [[0,0,0], [0,1,0], [0,2,0], [0,3,0], [0,0,1], [0,1,1], [0,2,1], [0,3,1]]
    ]
-}
