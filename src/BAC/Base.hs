{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module BAC.Base where

import Control.Monad (guard)
import Data.Bifunctor (bimap)
import Data.List (nub, nubBy, sort, sortOn)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe, fromJust)
import Data.Tuple (swap)
import Numeric.Natural (Natural)

import Utils.Utils ((|>), (.>), groupOn)
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

-- | Symbol of a node, representing an object of the corresponding category.
type Symbol = Natural

-- | The base symbol, representing an initial object.
base :: Symbol
base = 0

-- | Return all symbols of a node in ascending order.
symbols :: Node e -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> sort .> nub .> (base :)

-- * Others

cat :: Dict -> Dict -> Dict
cat = fmap . (!)

withDict :: Arrow v e -> Dict -> Arrow v e
withDict edge dict = edge {dict = dict}

withNode :: Arrow v e -> Node o -> Arrow v o
withNode edge node = edge {node = node}

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
  validateChildren
  && validateDicts
  && validateSup
  where
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

foldUnder :: Symbol -> (FoldUnderArgument e r -> r) -> (Node e -> Maybe r)
foldUnder sym f bac = case fold f' bac of
  InnerRes r -> Just r
  BoundaryRes r -> Just r
  OuterRes -> Nothing
  where
  f' arr results = case locate sym arr of
    Outer    -> OuterRes
    Boundary -> BoundaryRes $ f $ BoundaryArg arr
    Inner    -> InnerRes    $ f $ InnerArg    arr results

forUnder :: Symbol -> Node e -> (FoldUnderArgument e r -> r) -> Maybe r
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
mapUnder sym g = foldUnder sym go
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

findUnder :: Symbol -> (Location -> Arrow () e -> Bool) -> (Node e -> Maybe [Arrow () e])
findUnder sym f = foldUnder sym go .> fmap Map.elems
  where
  go arg =
    if f loc arr
    then Map.unions results |> Map.insert (symbolize arr) arr
    else Map.unions results
    where
    (arr, loc, results) = case arg of
      BoundaryArg arr -> (arr, Boundary, [])
      InnerArg arr results -> (arr, Inner, results |> mapMaybe toMaybe)
    toMaybe = \case
      InnerRes r -> Just r
      BoundaryRes r -> Just r
      OuterRes -> Nothing

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

  forUnder src bac $ \case
    BoundaryArg curr -> Node src_edges'
    InnerArg curr results -> Node $ do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withNode` res]

relabelObject :: Symbol -> Dict -> Node e -> Maybe (Node e)
relabelObject tgt mapping bac = do
  tgt_arr <- walk tgt (root bac)
  guard $ mapping ! base == base
  guard $ Map.keys mapping == symbols (node tgt_arr)
  forUnder tgt bac $ \case
    BoundaryArg curr -> Node $ do
      edge <- edges (node curr)
      let relabelled_dict = mapping `cat` dict edge
      [edge `withDict` relabelled_dict]
    InnerArg curr results -> Node $ do
      (res, edge) <- results `zip` edges (node curr)
      case res of
        OuterRes -> [edge]
        InnerRes res -> [edge `withNode` res]
        BoundaryRes res -> [edge `withDict` relabelled_dict `withNode` res]
          where
          unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
          relabelled_dict = dict edge `cat` unmapping
