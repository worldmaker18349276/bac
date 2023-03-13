{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Base where

import Control.Monad (guard)
import Data.Bifunctor (bimap)
import Data.List (nub, nubBy, sort, sortOn)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Tuple (swap)
import Numeric.Natural (Natural)

import Utils.Memoize (unsafeMemoizeWithKey)
import Utils.Utils (groupOn, (.>), (|>))

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
type Edge e = Arrow' e e

-- | Arrow of a bounded acyclic category, representing a downward functor.
type Arrow e = Arrow' () e

data Arrow' v e = Arrow' {dict :: Dict, node :: Node e, value :: v}
  deriving (Eq, Ord, Show)

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

cat :: Dict -> Dict -> Dict
cat = fmap . (!)

-- * Others

withDict :: Arrow' v e -> Dict -> Arrow' v e
withDict edge dict = edge {dict = dict}

withNode :: Arrow' v e -> Node o -> Arrow' v o
withNode edge node = edge {node = node}

withValue :: Arrow' v e -> w -> Arrow' w e
withValue edge value = edge {value = value}

asArrow :: Arrow' v e -> Arrow e
asArrow = (`withValue` ())

-- explore methods

data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

root :: Node e -> Arrow e
root bac = Arrow' {dict = id_dict, node = bac, value = ()}
  where
  id_dict = bac |> symbols |> fmap (\a -> (a, a)) |> Map.fromList

join :: Arrow' v e -> Arrow' w e -> Arrow e
join arr1 arr2 = asArrow $ arr2 `withDict` (dict arr1 `cat` dict arr2)

next :: Arrow' v e -> [Arrow e]
next arr = edges (node arr) |> fmap (join arr)

locate :: Symbol -> Arrow' v e -> Location
locate sym arr
  | symbolize arr == sym = Boundary
  | sym `elem` dict arr  = Inner
  | otherwise            = Outer

arrow :: Symbol -> Node e -> Maybe (Arrow e)
arrow sym = root .> go
  where
  go arr = case locate sym arr of
    Outer    -> Nothing
    Boundary -> Just (asArrow arr)
    Inner    -> Just $ arr |> next |> mapMaybe go |> head

arrow2 :: (Symbol, Symbol) -> Node e -> Maybe (Arrow e, Arrow e)
arrow2 (src, tgt) bac = do
  src_arr <- bac |> arrow src
  tgt_subarr <- node src_arr |> arrow tgt
  Just (src_arr, tgt_subarr)

symbolize :: Arrow' v e -> Symbol
symbolize = dict .> (! base)

symbolize2 :: (Arrow' v e, Arrow' w e) -> (Symbol, Symbol)
symbolize2 = symbolize `bimap` symbolize

nondecomposable :: Node e -> Symbol -> Bool
nondecomposable bac sym =
  (root bac |> locate sym |> (== Inner))
  && (edges bac |> all (locate sym .> (/= Inner)))

children :: Symbol -> Node e -> Maybe [(Arrow e, Edge e)]
children tgt bac = do
  tgt_arr <- bac |> arrow tgt
  Just $ edges (node tgt_arr) |> fmap (tgt_arr,) |> sortOn symbolize2

parents :: Symbol -> Node e -> Maybe [(Arrow e, Edge e)]
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
  is_parent = next .> any (locate tgt .> (== Boundary))

sameStruct :: Arrow' v e -> Arrow' w o -> Bool
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
    |> fmap (\node -> symbols node |> fmap (`arrow` node) |> fmap fromJust)
    |> zip (edges bac)
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (root bac :)
    |> sortOn symbolize
    |> groupOn symbolize
    |> all (nubBy sameStruct .> length .> (== 1))

-- fold methods

fold :: (Arrow e -> [r] -> r) -> (Node e -> r)
fold f = root .> fold'
  where
  fold' = memoize \curr -> f curr (curr |> next |> fmap fold')
  memoize = unsafeMemoizeWithKey symbolize

data Located s =
    AtOuter
  | AtBoundary
  | AtInner s
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

fromReachable :: a -> Located a -> Maybe a
fromReachable _ AtOuter     = Nothing
fromReachable a AtBoundary  = Just a
fromReachable _ (AtInner a) = Just a

fromInner :: Located a -> Maybe a
fromInner (AtInner a) = Just a
fromInner _           = Nothing

foldUnder ::
  Symbol
  -> (Arrow e -> [Located s] -> s)
  -> (Node e -> Located s)
foldUnder sym f = fold f'
  where
  f' curr results = case locate sym curr of
    Outer    -> AtOuter
    Boundary -> AtBoundary
    Inner    -> AtInner $ f curr results

modify ::
  ((Arrow e, Edge e) -> Node e' -> [Edge e'])
  -> (Node e -> Node e')
modify f =
  fold \curr results -> Node do
    (res, edge) <- results `zip` edges (node curr)
    f (curr, edge) res

modifyUnder ::
  Symbol
  -> ((Arrow e, Edge e) -> Located (Node e') -> [Edge e'])
  -> (Node e -> Located (Node e'))
modifyUnder sym f =
  foldUnder sym \curr results -> Node do
    (res, edge) <- results `zip` edges (node curr)
    f (curr, edge) res

map :: ((Arrow e, Edge e) -> o) -> (Node e -> Node o)
map f = modify \(curr, edge) res -> [edge `withValue` f (curr, edge) `withNode` res]

mapUnder :: Symbol -> (Location -> (Arrow e, Edge e) -> e) -> (Node e -> Maybe (Node e))
mapUnder sym f bac = do
  curr <- bac |> arrow sym
  let res0 = node curr
  fromReachable res0 $ bac |> modifyUnder sym \(curr, edge) -> \case
    AtOuter     -> [edge]
    AtBoundary  -> [edge `withValue` f Boundary (curr, edge) `withNode` res0]
    AtInner res -> [edge `withValue` f Inner    (curr, edge) `withNode` res]

find :: (Arrow e -> Bool) -> (Node e -> [Arrow e])
find f = Map.elems . fold \curr ->
  Map.unions .> if f curr then Map.insert (symbolize curr) curr else id

findUnder :: Symbol -> (Arrow e -> Bool) -> (Node e -> Maybe [Arrow e])
findUnder sym f bac =
  fromReachable [] $ fmap Map.elems $
    bac |> foldUnder sym \curr results ->
      results
      |> mapMaybe (fromReachable Map.empty)
      |> Map.unions
      |> if f curr then Map.insert (symbolize curr) curr else id

rewireEdges :: Symbol -> [(e, Symbol)] -> Node e -> Maybe (Node e)
rewireEdges src tgts bac = do
  src_arr <- bac |> arrow src
  let src_edges = edges (node src_arr)
  src_edges' <-
    tgts
    |> traverse (traverse (`arrow` node src_arr))
    |> fmap (fmap (\(value, arr) -> arr `withValue` value))
  let res0 = Node src_edges'

  let nd_syms = fmap symbolize .> filter (nondecomposable (node src_arr)) .> sort .> nub
  guard $ nd_syms src_edges == nd_syms src_edges'

  fromReachable res0 $ bac |> modifyUnder src \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge `withNode` res]
    AtBoundary -> [edge `withNode` res0]

relabelObject :: Symbol -> Dict -> Node e -> Maybe (Node e)
relabelObject tgt mapping bac = do
  tgt_arr <- bac |> arrow tgt
  guard $ mapping ! base == base
  guard $ Map.keys mapping == symbols (node tgt_arr)
  let res0 = Node do
        edge <- edges (node tgt_arr)
        let relabelled_dict = mapping `cat` dict edge
        [edge `withDict` relabelled_dict]
  fromReachable res0 $ bac |> modifyUnder tgt \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge `withNode` res]
    AtBoundary -> [edge `withDict` relabelled_dict `withNode` res0]
      where
      unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
      relabelled_dict = dict edge `cat` unmapping
