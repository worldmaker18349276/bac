{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Base where

import Control.Monad (guard)
import Data.Bifunctor (bimap, Bifunctor (second))
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
--   It should be validated by `validate . root`.
newtype Node e = Node {edges :: [Edge e]} deriving (Eq, Ord, Show)

-- | The edge of the tree representation of a bounded acyclic category.
--   The type variable `e` refers to the data carried by the edges.
--   See 'Arrow'' for detail.
type Edge e = Arrow' e e

-- | Arrow of a bounded acyclic category, representing a downward functor.
--   See 'Arrow'' for detail.
type Arrow e = Arrow' () e

-- | Arrow of a bounded acyclic category with a value.
--   It should be validated by `validate`.
data Arrow' v e = Arrow' {dict :: Dict, target :: Node e, value :: v}
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
symbols = edges .> concatMap (dict .> Map.elems) .> (base :) .> sort .> nub

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
root node = Arrow' {dict = id_dict, target = node, value = ()}
  where
  id_dict = node |> symbols |> fmap (\a -> (a, a)) |> Map.fromList

-- | Join two arrows into one arrow.
--   It may crashes if two arrows are not composable.
join :: Arrow' v e -> Arrow' w e -> Arrow e
join arr1 arr2 = arr2 {dict = dict arr1 `cat` dict arr2, value = ()}

-- | Extend an arrow by joining to the edges of the target node.
extend :: Arrow' v e -> [Arrow e]
extend arr = edges (target arr) |> fmap (join arr)

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
  | symbol arr == sym = Boundary
  | sym `elem` dict arr  = Inner
  | otherwise            = Outer

-- | Make a arrow pointing to the node referenced by the given symbol.
--   Return `Nothing` if it is outside the node.
--
--   Examples:
--
--   >>> arrow 3 cone
--   Just (Arrow' {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
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
--   Just (Arrow' {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
--
--   >>> fmap snd (arrow2 (3,2) cone)
--   Just (Arrow' {dict = fromList [(0,2)], target = ...
--
--   >>> arrow2 (1,2) cone
--   Nothing
arrow2 :: (Symbol, Symbol) -> Node e -> Maybe (Arrow e, Arrow e)
arrow2 (src, tgt) node = do
  src_arr <- node |> arrow src
  tgt_subarr <- target src_arr |> arrow tgt
  Just (src_arr, tgt_subarr)

-- | Find the symbol referencing to the given arrow.
--   It is the inverse of `arrow`:
--
--   > fmap symbol (arrow sym node) = Just sym
--
--   Examples:
--
--   >>> fmap symbol (arrow 3 cone)
--   Just 3
--
--   >>> fmap symbol (arrow 5 cone)
--   Nothing
symbol :: Arrow' v e -> Symbol
symbol = dict .> (! base)

-- | Find the pair of symbols referencing to the given 2-chain.
--   It is the inverse of `arrow2`:
--
--   > fmap symbol2 (arrow2 sym2 node) = Just sym2
--
--   Examples:
--
--   >>> fmap symbol2 (arrow2 (3,2) cone)
--   Just (3,2)
--
--   >>> fmap symbol2 (arrow2 (1,2) cone)
--   Nothing
symbol2 :: (Arrow' v e, Arrow' w e) -> (Symbol, Symbol)
symbol2 = symbol `bimap` symbol

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
nondecomposable node sym =
  (root node |> locate sym |> (/= Outer))
  && (edges node |> all (locate sym .> (/= Inner)))

-- ** Validation #validation#

-- | Check if two arrows have the same structure by ignoring the additional data they
--   stored.
sameStruct :: Arrow' v e -> Arrow' w o -> Bool
sameStruct arr1 arr2 =
  dict arr1 == dict arr2
  && length (edges (target arr1)) == length (edges (target arr2))
  && (edges (target arr1) `zip` edges (target arr2) |> all (uncurry sameStruct))

-- | Check if a node is valid.  See [Types]("BAC.Base#g:types") for detail.
--
--   Examples:
--
--   >>> validate (root cone)
--   True
--
--   >>> validate (root torus)
--   True
--
--   >>> validate (root crescent)
--   True
--
--   >>> fmap validate (arrow 3 cone)
--   Just True
validate :: Arrow' v e -> Bool
validate arr = validateChildren && validateDicts && validateSup
  where
  validateChildren = edges (target arr) |> all validate
  validateDicts = Map.keys (dict arr) == symbols (target arr)
  validateSup =
    extend arr
    |> fmap (\a -> (a, a))
    |> fmap (second (target .> descendants))
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (arr {value = ()} :)
    |> sortOn symbol
    |> groupOn symbol
    |> all (nubBy sameStruct .> length .> (== 1))
  descendants node = symbols node |> fmap (`arrow` node) |> fmap fromJust

-- * Folding #folding#

-- | A value labeled by the relative position of the node.
data Located r = AtOuter | AtBoundary | AtInner r
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Retrieve a reachable value, or return nothing if it is unreachable.
fromReachable :: a -> Located a -> Maybe a
fromReachable _ AtOuter     = Nothing
fromReachable a AtBoundary  = Just a
fromReachable _ (AtInner a) = Just a

-- | Retrieve the inner variant of a located value, otherwise return nothing.
fromInner :: Located a -> Maybe a
fromInner (AtInner a) = Just a
fromInner _           = Nothing

-- | Fold a BAC.  All nodes are visited only once according to symbols.
fold ::
  (Arrow e -> [r] -> r)  -- ^ The function to reduce a node and the results from its child
                         --   nodes into a value.
  -> Node e              -- ^ The root node of BAC to fold.
  -> r                   -- ^ The folding result.
fold f = root .> fold'
  where
  fold' = memoize \curr -> f curr (curr |> extend |> fmap fold')
  memoize = unsafeMemoizeWithKey symbol

-- | Fold a BAC under a node.
foldUnder ::
  Symbol                            -- ^ The symbol referencing to the boundary.
  -> (Arrow e -> [Located r] -> r)  -- ^ The reduce function.  Where the results of child
                                    --   nodes are labeled by `Located`.
  -> Node e                         -- ^ The root node of BAC to fold.
  -> Located r                      -- ^ The folding result, which is labeled by `Located`.
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
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

modifyUnder ::
  Symbol
  -> ((Arrow e, Edge e) -> Located (Node e') -> [Edge e'])
  -> (Node e -> Located (Node e'))
modifyUnder sym f =
  foldUnder sym \curr results -> Node do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

map :: ((Arrow e, Edge e) -> o) -> (Node e -> Node o)
map f = modify \(curr, edge) res -> [edge {value = f (curr, edge), target = res}]

mapUnder :: Symbol -> (Location -> (Arrow e, Edge e) -> e) -> (Node e -> Maybe (Node e))
mapUnder sym f node = do
  curr <- node |> arrow sym
  let res0 = target curr
  fromReachable res0 $ node |> modifyUnder sym \(curr, edge) -> \case
    AtOuter     -> [edge]
    AtBoundary  -> [edge {value = f Boundary (curr, edge), target = res0}]
    AtInner res -> [edge {value = f Inner    (curr, edge), target = res}]

find :: (Arrow e -> Bool) -> (Node e -> [Arrow e])
find f = Map.elems . fold \curr ->
  Map.unions .> if f curr then Map.insert (symbol curr) curr else id

findUnder :: Symbol -> (Arrow e -> Bool) -> (Node e -> Maybe [Arrow e])
findUnder sym f =
  fromReachable [] . fmap Map.elems .
    foldUnder sym \curr results ->
      results
      |> mapMaybe fromInner
      |> Map.unions
      |> if f curr then Map.insert (symbol curr) curr else id

parents :: Symbol -> Node e -> Maybe [(Arrow e, Edge e)]
parents tgt node = do
  arrs <- findUnder tgt is_parent node
  Just $
    arrs
    |> fmap (target .> edges)
    |> zip arrs
    |> concatMap sequence
    |> filter (uncurry join .> locate tgt .> (== Boundary))
    |> sortOn symbol2
  where
  is_parent = extend .> any (locate tgt .> (== Boundary))

-- * Non-Categorical Operations #operations#

rewireEdges :: Symbol -> [(e, Symbol)] -> Node e -> Maybe (Node e)
rewireEdges src tgts node = do
  src_arr <- node |> arrow src
  let src_edges = edges (target src_arr)
  src_edges' <-
    tgts
    |> traverse (traverse (`arrow` target src_arr))
    |> fmap (fmap (\(value, arr) -> arr {value = value}))
  let res0 = Node src_edges'

  let nd_symbols = fmap symbol .> filter (nondecomposable (target src_arr))
  guard $ nd_symbols src_edges == nd_symbols src_edges'

  fromReachable res0 $ node |> modifyUnder src \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {target = res}]
    AtBoundary -> [edge {target = res0}]

relabelObject :: Symbol -> Dict -> Node e -> Maybe (Node e)
relabelObject tgt mapping node = do
  tgt_arr <- node |> arrow tgt
  guard $ base `Map.member` mapping && mapping ! base == base
  guard $ Map.keys mapping == symbols (target tgt_arr)
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  let res0 = Node [edge {dict = mapping `cat` dict edge} | edge <- edges (target tgt_arr)]
  fromReachable res0 $ node |> modifyUnder tgt \(_, edge) -> \case
    AtOuter -> [edge]
    AtInner res -> [edge {target = res}]
    AtBoundary -> [edge {dict = dict edge `cat` unmapping, target = res0}]
