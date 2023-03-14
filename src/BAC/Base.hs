{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
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
-- The example code below runs with the following settings:
--
-- >>> import BAC.YAML
-- >>> import BAC.Examples (cone, torus, crescent)

-- * Basic #basic#

-- ** Types #types#
--
-- $doc
-- Tree representation of a bounded acyclic category.
--
-- A bounded acyclic category can be represented as a tree structure with implicitly
-- shared nodes.
--
-- Edges of such structure have dictionaries, which obey three laws:
--
-- 1.  __totality__: the dictionary of an edge should be a mapping from all valid symbols
--     in the child node to valid symbols in the parent node.
-- 2.  __surjectivity__: all valid symbols should be covered by the dictionaries of
--     outgoing edges, except the base symbol.
-- 3.  __supportivity__: if dictionaries of given two paths with the same starting node
--     map the base symbol to the same symbol, then they should have the same dictionary
--     and target node.  Note that null paths also count.
--
-- See my paper for a detailed explanation.

-- | The node of the tree representation of a bounded acyclic category.
--   The type variable `e` refers to the data carried by the edges.
newtype Node e = Node {edges :: [Edge e]} deriving (Eq, Ord, Show)

-- | The edge of the tree representation of a bounded acyclic category.
--   The type variable `e` refers to the data carried by the edges.
--   See 'Arrow'' for detail.
type Edge e = Arrow' e e

-- | Arrow of a bounded acyclic category, representing a downward functor.
--   See 'Arrow'' for detail.
type Arrow e = Arrow' () e

-- | Arrow of a bounded acyclic category with a value.
data Arrow' v e = Arrow'
  {
    -- | The dictionary of the arrow.
    --   Its keys should be the symbols of the target node, and it should map the base
    --   symbol to the unique symbol comparing with others elements of this map.
    dict :: Dict,
    -- | The target node.
    node :: Node e,
    -- | The value carried by this arrow.
    value :: v
  }
  deriving (Eq, Ord, Show)

-- | Dictionary of an arrow, representing mapping between objects.
type Dict = Map Symbol Symbol

-- | Symbol of a node, representing an object of the corresponding category.
type Symbol = Natural

-- | The base symbol, representing an initial object.
base :: Symbol
base = 0

-- | Return all symbols of a node in ascending order.  The first one is the base symbol.
--
--   Examples:
--
--   >>> symbols cone
--   [0,1,2,3,4,6]
--
--   >>> symbols torus
--   [0,1,2,3,5]
--
--   >>> symbols crescent
--   [0,1,2,3,6]
symbols :: Node e -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> sort .> nub .> (base :)

-- | Concatenate two dictionaries:
--
--   > (a `cat` b) ! i = a ! (b ! i)
--
--   It may crash if given dictionaries are not composable.
cat :: Dict -> Dict -> Dict
cat = fmap . (!)

-- ** Traversing #traversing#

-- | The relative location between nodes.
data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

-- | Return root arrow of a node.
root :: Node e -> Arrow e
root bac = Arrow' {dict = id_dict, node = bac, value = ()}
  where
  id_dict = bac |> symbols |> fmap (\a -> (a, a)) |> Map.fromList

-- | Join two arrows into one arrow.
--   It may crashes if two arrows are not composable.
join :: Arrow' v e -> Arrow' w e -> Arrow e
join arr1 arr2 = arr2 {dict = dict arr1 `cat` dict arr2, value = ()}

-- | Extend an arrow by joining to the edges of the target node.
extend :: Arrow' v e -> [Arrow e]
extend arr = edges (node arr) |> fmap (join arr)

-- | Find the relative Location of the node referenced by the given symbol with respect to
--   a given arrow.
--
--   Examples:
--
--   >>> locate 2 (root cone)
--   Inner
--
--   >>> locate 0 (root cone)
--   Boundary
--
--   >>> locate 5 (root cone)
--   Outer
locate :: Symbol -> Arrow' v e -> Location
locate sym arr
  | symbolize arr == sym = Boundary
  | sym `elem` dict arr  = Inner
  | otherwise            = Outer

-- | Make a arrow pointing to the node referenced by the given symbol.
--   Return `Nothing` if it is outside the node.
--
--   Examples:
--
--   >>> arrow 3 cone
--   Just (Arrow' {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], node = ...
--
--   >>> arrow 5 cone
--   Nothing
arrow :: Symbol -> Node e -> Maybe (Arrow e)
arrow sym = root .> go
  where
  go arr = case locate sym arr of
    Outer    -> Nothing
    Boundary -> Just arr
    Inner    -> Just $ arr |> extend |> mapMaybe go |> head

-- | Make a 2-chain by given pair of symbols.
--
--   Examples:
--
--   >>> fmap fst (arrow2 (3,2) cone)
--   Just (Arrow' {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], node = ...
--
--   >>> fmap snd (arrow2 (3,2) cone)
--   Just (Arrow' {dict = fromList [(0,2)], node = ...
--
--   >>> arrow2 (1,2) cone
--   Nothing
arrow2 :: (Symbol, Symbol) -> Node e -> Maybe (Arrow e, Arrow e)
arrow2 (src, tgt) bac = do
  src_arr <- bac |> arrow src
  tgt_subarr <- node src_arr |> arrow tgt
  Just (src_arr, tgt_subarr)

-- | Find the symbol referencing to the given arrow.
--   It is the inverse of `arrow`:
--
--   > fmap symbolize (arrow sym bac) = Just sym
--
--   Examples:
--
--   >>> fmap symbolize (arrow 3 cone)
--   Just 3
--
--   >>> fmap symbolize (arrow 5 cone)
--   Nothing
symbolize :: Arrow' v e -> Symbol
symbolize = dict .> (! base)

-- | Find the pair of symbols referencing to the given 2-chain.
--   It is the inverse of `arrow2`:
--
--   > fmap symbolize2 (arrow2 sym2 bac) = Just sym2
--
--   Examples:
--
--   >>> fmap symbolize2 (arrow2 (3,2) cone)
--   Just (3,2)
--
--   >>> fmap symbolize2 (arrow2 (1,2) cone)
--   Nothing
symbolize2 :: (Arrow' v e, Arrow' w e) -> (Symbol, Symbol)
symbolize2 = symbolize `bimap` symbolize

-- | Check if the given symbol reference to a nondecomposable initial morphism.
--
--   Examples:
--
--   >>> nondecomposable cone 3
--   True
--
--   >>> nondecomposable cone 4
--   False
nondecomposable :: Node e -> Symbol -> Bool
nondecomposable bac sym =
  (root bac |> locate sym |> (== Inner))
  && (edges bac |> all (locate sym .> (/= Inner)))

-- ** Validation #validation#

-- | Check if two arrows have the same structure by ignoring the additional data they
--   stored.
sameStruct :: Arrow' v e -> Arrow' w o -> Bool
sameStruct arr1 arr2 =
  dict arr1 == dict arr2
  && length (edges (node arr1)) == length (edges (node arr2))
  && (edges (node arr1) `zip` edges (node arr2) |> all (uncurry sameStruct))

-- | Check if a node is valid.  See [Types]("BAC.Base#g:types") for detail.
--
--   Examples:
--
--   >>> validate cone
--   True
--
--   >>> validate torus
--   True
--
--   >>> validate crescent
--   True
validate :: Node e -> Bool
validate bac = validateChildren && validateDicts && validateSup
  where
  validateChildren = edges bac |> fmap node |> all validate
  validateDicts =
    edges bac
    |> all (\edge -> Map.keys (dict edge) == symbols (node edge))
  validateSup =
    edges bac
    |> fmap (node .> descendants)
    |> zip (edges bac)
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (root bac :)
    |> sortOn symbolize
    |> groupOn symbolize
    |> all (nubBy sameStruct .> length .> (== 1))
  descendants bac = symbols bac |> fmap (`arrow` bac) |> fmap fromJust

-- * Folding #folding#

fold :: (Arrow e -> [r] -> r) -> (Node e -> r)
fold f = root .> fold'
  where
  fold' = memoize \curr -> f curr (curr |> extend |> fmap fold')
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

scan ::
  ((Arrow e, Edge e) -> Node e' -> [Edge e'])
  -> (Node e -> Node e')
scan f =
  fold \curr results -> Node do
    (res, edge) <- results `zip` edges (node curr)
    f (curr, edge) res

scanUnder ::
  Symbol
  -> ((Arrow e, Edge e) -> Located (Node e') -> [Edge e'])
  -> (Node e -> Located (Node e'))
scanUnder sym f =
  foldUnder sym \curr results -> Node do
    (res, edge) <- results `zip` edges (node curr)
    f (curr, edge) res

map :: ((Arrow e, Edge e) -> o) -> (Node e -> Node o)
map f = scan \(curr, edge) res -> [edge {value = f (curr, edge), node = res}]

mapUnder :: Symbol -> (Location -> (Arrow e, Edge e) -> e) -> (Node e -> Maybe (Node e))
mapUnder sym f bac = do
  curr <- bac |> arrow sym
  let res0 = node curr
  fromReachable res0 $ bac |> scanUnder sym \(curr, edge) -> \case
    AtOuter     -> [edge]
    AtBoundary  -> [edge {value = f Boundary (curr, edge), node = res0}]
    AtInner res -> [edge {value = f Inner    (curr, edge), node = res}]

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
  is_parent = extend .> any (locate tgt .> (== Boundary))

-- * Non-Categorical Operations #operations#

rewireEdges :: Symbol -> [(e, Symbol)] -> Node e -> Maybe (Node e)
rewireEdges src tgts bac = do
  src_arr <- bac |> arrow src
  let src_edges = edges (node src_arr)
  src_edges' <-
    tgts
    |> traverse (traverse (`arrow` node src_arr))
    |> fmap (fmap (\(value, arr) -> arr {value = value}))
  let res0 = Node src_edges'

  let nd_syms = fmap symbolize .> filter (nondecomposable (node src_arr)) .> sort .> nub
  guard $ nd_syms src_edges == nd_syms src_edges'

  fromReachable res0 $ bac |> scanUnder src \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {node = res}]
    AtBoundary -> [edge {node = res0}]

relabelObject :: Symbol -> Dict -> Node e -> Maybe (Node e)
relabelObject tgt mapping bac = do
  tgt_arr <- bac |> arrow tgt
  guard $ mapping ! base == base
  guard $ Map.keys mapping == symbols (node tgt_arr)
  let res0 = Node do
        edge <- edges (node tgt_arr)
        let relabelled_dict = mapping `cat` dict edge
        [edge {dict = relabelled_dict}]
  fromReachable res0 $ bac |> scanUnder tgt \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {node = res}]
    AtBoundary -> [edge {dict = relabelled_dict, node = res0}]
      where
      unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
      relabelled_dict = dict edge `cat` unmapping
