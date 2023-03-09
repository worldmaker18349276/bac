{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module BAC.Class where

import Control.Monad (guard)
import qualified Control.Monad as Monad
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Foldable (for_)
import Data.List (delete, elemIndices, findIndex, nub, nubBy, sort, sortOn, transpose)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, fromJust)
import Data.Traversable (for)
import Data.Tuple (swap)

import Utils.Utils
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Memoize (unsafeMemoizeWithKey)

-- $setup
-- The examples run with the following settings:
-- 
-- >>> import BAC.YAML

-- * Basic

-- ** BAC
--
-- $doc
-- Tree representation of a bounded acyclic category.
-- ...

-- | The node of the tree representation of a bounded acyclic category.
--   The type variable 'e' refers to the data carried by the edges.
newtype Node e = Node {edges :: [Edge e]} deriving (Eq, Ord, Show)

-- | The edge of the tree representation of a bounded acyclic category.
--   The type variable 'e' refers to the data carried by the edges.
type Edge e = Arrow e e

-- | Arrow of a bounded acyclic category, representing a downward functor.
data Arrow v e = Arrow {dict :: Dict, node :: Node e, value :: v} deriving (Eq, Ord, Show)

-- | Dictionary of an arrow, representing mapping between objects.
type Dict = Map Symbol Symbol

-- ** Symbols
--
-- $doc
-- Symbol of a node ...

-- | Symbol of a node, representing an object of the corresponding category.
--   It is implemented as a list of integers.
newtype Symbol = Symbol [Integer] deriving (Eq, Ord, Show)

-- | The base symbol, representing an initial object.
base :: Symbol
base = Symbol []

-- | Return all symbols of a node in ascending order.
symbols :: Node e -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> sort .> nub .> (base :)

-- | Check if given symbols are valid.
--   Valid symbols in a node should be comparable in lexical order without ambiguity (it
--   never runs to comparison of lengths), except the base symbol, which should be the
--   smallest one.
-- 
--   Examples:
-- 
--   >>> isValidSymbols [Symbol []]
--   True
-- 
--   >>> isValidSymbols [Symbol [], Symbol [0], Symbol [1,2], Symbol [1,4]]
--   True
-- 
--   >>> isValidSymbols [Symbol [], Symbol [0], Symbol [0,2]]
--   False
isValidSymbols :: [Symbol] -> Bool
isValidSymbols syms = head == [base] && all validate (tail `zip` drop 1 tail)
  where
  sorted_syms = sort syms
  head = take 1 sorted_syms
  tail = drop 1 sorted_syms
  validate (Symbol (a:r), Symbol (b:s)) = a /= b || validate (Symbol r, Symbol s)
  validate _ = False

-- | Modify a symbol by function on list of integers.
relabel :: ([Integer] -> [Integer]) -> (Symbol -> Symbol)
relabel f (Symbol a) = Symbol (f a)

-- | Make a valid symbol according to a list of valid symbols, so that it can be added to
--   it.
makeNewSymbol :: [Symbol] -> Symbol
makeNewSymbol =
  concatMap (\(Symbol nums) -> nums |> take 1)
  .> fmap (+ 1)
  .> (0 :)
  .> maximum
  .> (: [])
  .> Symbol

-- | Split a symbol into multiples so they can be used to replace the symbol in a list of
--   valid symbols.
splitSymbol :: Symbol -> [Integer] -> [Symbol]
splitSymbol s = fmap (\num -> relabel (++ [num]) s)

--   (isValidSymbols syms && sym /= base) -> isValidSymbols (delete sym syms)
--   isValidSymbols syms -> isValidSymbols (syms ++ [makeNewSymbol syms])
--   (isValidSymbols syms && sym /= base && sym `elem` syms)
--     -> isValidSymbols (delete sym syms ++ splitSymbol sym nums)

-- * Others

cat :: Dict -> Dict -> Dict
cat = fmap . (!)

withDict :: Arrow v e -> Dict -> Arrow v e
withDict edge dict = edge {dict = dict}

withNode :: Arrow v e -> Node o -> Arrow v o
withNode edge node = edge {node = node}

withEdges :: Node e -> [Edge o] -> Node o
withEdges bac edges = bac {edges = edges}

asArrow :: Arrow v e -> Arrow () e
asArrow edge = edge {value = ()}

-- explore methods

data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

root :: Node e -> Arrow () e
root bac = Arrow {dict = id_dict, node = bac, value = ()}
  where
  id_dict = bac |> symbols |> fmap (\a -> (a, a)) |> Map.fromList

join :: Arrow v e -> Arrow w e -> Arrow () e
join arr1 arr2 = asArrow $ arr2 `withDict` (dict arr1 `cat` dict arr2)

next :: Arrow v e -> [Arrow () e]
next arr = edges (node arr) |> fmap (join arr)

locate :: Symbol -> Arrow v e -> Location
locate sym arr
  | symbolize arr == sym = Boundary
  | sym `elem` dict arr  = Inner
  | otherwise            = Outer

walk :: Symbol -> Arrow v e -> Maybe (Arrow () e)
walk sym arr = case locate sym arr of
  Outer    -> Nothing
  Boundary -> Just (asArrow arr)
  Inner    -> Just $ arr |> next |> mapMaybe (walk sym) |> head

walk2 :: (Symbol, Symbol) -> Arrow v e -> Maybe (Arrow () e, Arrow () e)
walk2 (src, tgt) arr = do
  src_arr <- walk src arr
  tgt_subarr <- walk tgt (root (node src_arr))
  Just (src_arr, tgt_subarr)

symbolize :: Arrow v e -> Symbol
symbolize = dict .> (! base)

symbolize2 :: (Arrow v e, Arrow w e) -> (Symbol, Symbol)
symbolize2 = symbolize `bimap` symbolize

walkAll :: Symbol -> Arrow v e -> [Arrow () e]
walkAll sym arr = case locate sym arr of
  Outer    -> []
  Boundary -> [asArrow arr]
  Inner    -> arr |> next |> concatMap (walkAll sym)

isNondecomposable :: Node e -> Symbol -> Bool
isNondecomposable bac sym =
  locate sym (root bac) == Inner
  && all (locate sym .> (/= Inner)) (edges bac)

children :: Symbol -> Node e -> Maybe [(Arrow () e, Edge e)]
children tgt bac = do
  tgt_arr <- walk tgt (root bac)
  Just $ edges (node tgt_arr) |> fmap (tgt_arr,) |> sortOn symbolize2

parents :: Symbol -> Node e -> Maybe [(Arrow () e, Edge e)]
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

sameStruct :: Arrow v e -> Arrow w o -> Bool
sameStruct arr1 arr2 =
  dict arr1 == dict arr2
  && length (edges (node arr1)) == length (edges (node arr2))
  && (edges (node arr1) `zip` edges (node arr2) |> all (uncurry sameStruct))

validate :: Node e -> Bool
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

fold :: (Arrow () e -> [r] -> r) -> (Node e -> r)
fold f = root .> fold'
  where
  fold' = memoize $ \arr -> f arr (arr |> next |> fmap fold')
  memoize = unsafeMemoizeWithKey symbolize

data FoldUnderResult r = InnerRes r | BoundaryRes r | OuterRes
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
data FoldUnderArgument e r =
  InnerArg (Arrow () e) [FoldUnderResult r] | BoundaryArg (Arrow () e)
  deriving (Functor, Foldable, Traversable)

toMaybe :: FoldUnderResult r -> Maybe r
toMaybe (InnerRes r) = Just r
toMaybe (BoundaryRes r) = Just r
toMaybe OuterRes = Nothing

foldUnder :: Symbol -> (FoldUnderArgument e r -> r) -> (Node e -> FoldUnderResult r)
foldUnder sym f = fold f'
  where
  f' arr results = case locate sym arr of
    Outer    -> OuterRes
    Boundary -> BoundaryRes $ f $ BoundaryArg arr
    Inner    -> InnerRes    $ f $ InnerArg    arr results

forUnder :: Symbol -> Node e -> (FoldUnderArgument e r -> r) -> FoldUnderResult r
forUnder sym = flip (foldUnder sym)

data FoldUnderResult' r s = InnerRes' r | BoundaryRes' s | OuterRes'

foldUnder'
  :: Symbol
  -> (Arrow () e -> [FoldUnderResult' r s] -> r)
  -> (Arrow () e                           -> s)
  -> (Node e -> FoldUnderResult' r s)
foldUnder' sym f_inner f_boundary = fold f'
  where
  f' arr results = case locate sym arr of
    Outer    -> OuterRes'
    Boundary -> BoundaryRes' $ f_boundary arr
    Inner    -> InnerRes'    $ f_inner    arr results

map :: ((Arrow () e, Edge e) -> o) -> (Node e -> Node o)
map g = fold $ \arr results ->
  edges (node arr)
  |> fmap (\edge -> edge {value = g (arr, edge)})
  |> (`zip` results)
  |> fmap (uncurry withNode)
  |> Node

mapUnder
  :: Symbol
  -> (Location -> (Arrow () e, Edge e) -> e)
  -> (Node e -> Maybe (Node e))
mapUnder sym g = foldUnder sym go .> toMaybe
  where
  go = \case
    BoundaryArg curr -> Node {edges = edges (node curr)}
    InnerArg curr results -> Node {edges = edges'}
      where
      edges' = do
        (edge, res) <- edges (node curr) `zip` results
        case res of
          BoundaryRes res -> [edge {value = g Boundary (curr, edge)} `withNode` res]
          InnerRes res -> [edge {value = g Inner (curr, edge)} `withNode` res]
          OuterRes -> [edge]

find :: (Arrow () e -> Bool) -> (Node e -> [Arrow () e])
find f = fold go .> Map.elems
  where
  go arr results =
    if f arr
    then Map.unions results |> Map.insert (symbolize arr) arr
    else Map.unions results

findUnder
  :: Symbol -> (Location -> Arrow () e -> Bool) -> (Node e -> Maybe [Arrow () e])
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

rewireEdges :: Symbol -> [(e, Symbol)] -> Node e -> Maybe (Node e)
rewireEdges src tgts bac = do
  src_arr <- walk src (root bac)
  let src_edges = edges (node src_arr)
  src_edges' <-
    tgts
    |> traverse (traverse (`walk` root (node src_arr)))
    |> fmap (fmap (\(value, arr) -> arr {value = value}))
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

relabelObject :: Symbol -> Dict -> Node e -> Maybe (Node e)
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

empty :: Node e
empty = Node {edges = []}

singleton :: e -> Integer -> Node e
singleton val num = Node {edges = [new_edge]}
  where
  new_sym = Symbol [num]
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
  -> Integer
  -> Node e -> Maybe (Edge e, Map (Symbol, Symbol) (Symbol, Symbol))
prepareForAddingMorphism src tgt src_alts tgt_alts val num bac = do
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

splitMorphism :: (Symbol, Symbol) -> [Integer] -> Node e -> Maybe (Node e)
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

partitionObject :: Node e -> [[Symbol]]
partitionObject bac = links |> bipartiteEqclass |> fmap (snd .> sort) |> sort
  where
  links = do
    arr <- edges bac
    let sym0 = symbolize arr
    sym <- dict arr |> Map.elems
    [(sym0, sym)]

splitObject :: Symbol -> [Integer] -> Node e -> Maybe (Node e)
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

splitCategory :: [Integer] -> Node e -> Maybe [Node e]
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

mergeObjects :: Map Integer Symbol -> Node e -> Maybe (Node e)
mergeObjects tgts bac = do
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
  let merged_node = mergeCategories tgt_nodes

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

mergeCategories :: Map Integer (Node e) -> Node e
mergeCategories bacs = Node {edges = merged_edges}
  where
  merged_edges = do
    (num, bac) <- Map.toList bacs
    edge <- edges bac
    let dict' = dict edge |> fmap (relabel (num :))
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
  -> (Integer, Integer)
  -> (e, e)
  -> Node e -> Maybe (Node e)
insertMorphism (src, tgt) (num1, num2) (val1, val2) bac = do
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
      let new_outedge = Arrow {dict = new_outdict, node = node tgt_arr, value = val2}
      let new_node = Node {edges = [new_outedge]}
      let new_indict = dict tgt_arr |> Map.insert new_sym2 tgt |> Map.insert base new_sym1
      Just $ Arrow {dict = new_indict, node = new_node, value = val1}
    Nothing ->
      Just $ Arrow {dict = Map.singleton base new_sym1, node = empty, value = val1}

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

