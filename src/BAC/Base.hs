{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}

module BAC.Base where

import Control.Monad (guard)
import Data.Bifunctor (bimap, Bifunctor (second))
import Data.Foldable (toList)
import Data.List.Extra (groupSortOn, nubSort, allSame, nubSortOn)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe, listToMaybe, fromMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (dupe)
import Data.Functor (void)
import Numeric.Natural (Natural)
import GHC.Stack (HasCallStack)

import Utils.Memoize (unsafeMemoizeWithKey)
import Utils.Utils ((.>), (|>), guarded, orEmpty)
import Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet)

-- $setup
-- The example code below runs with the following settings:
--
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Map (fromList)

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
--   It should be validated by @validate . root@.
newtype Node e = Node {edges :: [Edge e]} deriving (Eq, Ord, Show, Functor)

-- | The edge of the tree representation of a bounded acyclic category.
--   The type variable `e` refers to the data carried by the edges.
type Edge e = (e, Arrow e)

-- | Arrow of a bounded acyclic category, representing a downward functor.
--   It should be validated by `validate`.
data Arrow e = Arrow {dict :: Dict, target :: Node e} deriving (Eq, Ord, Show, Functor)

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
--   [0,1,2,3,4]
symbols :: Node e -> [Symbol]
symbols = edges .> fmap snd .> concatMap (dict .> Map.elems) .> (base :) .> nubSort

-- | Concatenate two dictionaries:
--
--   > (a `cat` b) ! i = a ! (b ! i)
--
--   It may crash if given dictionaries are not composable.
cat :: HasCallStack => Dict -> Dict -> Dict
cat = fmap . (!)

-- ** Arrow #arrow#

-- | The relative location between nodes.
data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

-- | Return root arrow of a node.
root :: Node e -> Arrow e
root node = Arrow {dict = id_dict, target = node}
  where
  id_dict = node |> symbols |> fmap dupe |> Map.fromList

-- | Join two arrows into one arrow.
--   It may crashes if two arrows are not composable.
join :: HasCallStack => Arrow e -> Arrow e -> Arrow e
join arr1 arr2 = arr2 {dict = dict arr1 `cat` dict arr2}

-- | Divide two arrows.  The first is divisor and the second is the dividend, and they
--   should start at the same node.
--   It obeys the following law:
--
--   > arr23 `elem` divide arr12 arr13  ->  arr12 `join` arr23 == arr13
divide :: Arrow e -> Arrow e -> [Arrow e]
divide arr12 arr13 =
  arr12
  |> dict
  |> Map.toList
  |> filter (snd .> (== symbol arr13))
  |> fmap fst
  |> nubSort
  |> fmap ((`arrow` target arr12) .> fromJust)

-- | Extend an arrow by joining to the edges of the target node.
extend :: Arrow e -> [Arrow e]
extend arr = edges (target arr) |> fmap snd |> fmap (join arr)

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
locate :: Symbol -> Arrow e -> Location
locate sym arr
  | symbol arr == sym   = Boundary
  | sym `elem` dict arr = Inner
  | otherwise           = Outer

-- | Make a arrow pointing to the node referenced by the given symbol.
--   Return `Nothing` if it is outside the node.
--
--   Examples:
--
--   >>> arrow 3 cone
--   Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
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
symbol :: Arrow e -> Symbol
symbol = dict .> (! base)

-- ** Tuple of Arrows

-- | Make a 2-chain by given pair of symbols.
--
--   Examples:
--
--   >>> fmap fst (arrow2 (3,2) cone)
--   Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
--
--   >>> fmap snd (arrow2 (3,2) cone)
--   Just (Arrow {dict = fromList [(0,2)], target = ...
--
--   >>> arrow2 (1,2) cone
--   Nothing
arrow2 :: (Symbol, Symbol) -> Node e -> Maybe (Arrow e, Arrow e)
arrow2 (src, tgt) node = do
  src_arr <- node |> arrow src
  tgt_subarr <- target src_arr |> arrow tgt
  return (src_arr, tgt_subarr)

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
symbol2 :: (Arrow e, Arrow e) -> (Symbol, Symbol)
symbol2 = symbol `bimap` symbol

-- | Divide two tuples of arrows.  The first is divisor and the second is the dividend,
--   and they should start and end at the same node.
--   It obeys the following laws:
--
--   > arr12 `join` arr24  ==  arr13 `join` arr34
--   > arr23 `elem` divide2 (arr12, arr24) (arr13, arr34)
--   > ->  arr12 `join` arr23 == arr13
--   > &&  arr23 `join` arr34 == arr34
divide2 :: (Arrow e, Arrow e) -> (Arrow e, Arrow e) -> [Arrow e]
divide2 (arr12, arr24) (arr13, arr34) =
  arr12 `divide` arr13 |> filter (\arr23 -> symbol (arr23 `join` arr34) == symbol arr24)

-- | Extend a tuple of arrows.
--   It obeys the following law:
--
--   > (arr13, arr34) `elem` extend2 (arr12, arr24)
--   > ->  arr13 `elem` extend arr12
--   > &&  arr12 `join` arr24 == arr13 `join` arr34
extend2 :: (Arrow e, Arrow e) -> [(Arrow e, Arrow e)]
extend2 (arr1, arr2) =
  edges (target arr1)
  |> filter (snd .> locate (symbol arr2) .> (/= Outer))
  |> fmap snd
  |> concatMap (\arr -> arr `divide` arr2 |> fmap (arr1 `join` arr,))

-- | Find prefix edges of a node under a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` prefix node sym
--   > ->  symbol (arr1 `join` arr2) == sym
--   > &&  (_, arr1) `elem` edges node
prefix :: Node e -> Symbol -> [(Arrow e, Arrow e)]
prefix node sym =
  arrow sym node
  |> maybe [] \tgt_arr ->
    edges node
    |> fmap snd
    |> mapMaybe (\arr -> divide arr tgt_arr |> listToMaybe |> fmap (arr,))

-- | Find suffix edges of a node under a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` suffix node sym
--   > ->  symbol (arr1 `join` arr2) == sym
--   > &&  (_, arr2) `elem` edges (target arr1)
suffix :: Node e -> Symbol -> [(Arrow e, Arrow e)]
suffix node sym =
  node
  |> findMapUnder sym (\b r _ -> orEmpty (not b) r)
  |> fromMaybe [] 

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
  && (edges node |> fmap snd |> all (locate sym .> (/= Inner)))

ndEdges :: Node e -> [Arrow e]
ndEdges node =
  edges node
  |> fmap snd
  |> filter (symbol .> nondecomposable node)
  |> nubSortOn symbol

-- ** Validation #validation#

-- | Check if an arrow is valid.  To validate a node, try @validate (root node)@.
--   See [Types]("BAC.Base#g:types") for detail.
validate :: Arrow e -> Bool
validate arr = validateDicts && validateSup
  where
  validateDicts = Map.keys (dict arr) == symbols (target arr)
  validateSup =
    extend arr
    |> fmap dupe
    |> fmap (second (target .> descendants))
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (arr :)
    |> fmap void
    |> groupSortOn symbol
    |> all allSame
  descendants node = symbols node |> fmap (`arrow` node) |> fmap fromJust

-- | Check if an arrow is valid in depth.  All descendant nodes will be checked.
--
--   Examples:
--
--   >>> validateAll (root cone)
--   True
--
--   >>> validateAll (root torus)
--   True
--
--   >>> validateAll (root crescent)
--   True
--
--   >>> fmap validateAll (arrow 3 cone)
--   Just True
validateAll :: Arrow e -> Bool
validateAll arr = validateChildren && validate arr
  where
  validateChildren = edges (target arr) |> fmap snd |> all validateAll

-- | Check structural equality of nodes up to rewiring.
--   The symbols of nodes should be the same, and equality of child nodes are not checked.
sameStruct :: [Node e] -> Bool
sameStruct = fmap ndEdges .> fmap (fmap dict) .> allSame

canonicalize :: Node e -> [Dict]
canonicalize =
  ndEdges
  .> fmap dict
  .> fmap Map.elems
  .> canonicalizeEqlistSet
  .> fmap (base :)
  .> fmap ((`zip` [base..]) .> Map.fromList)

canonicalizeArrow :: Arrow e -> [Dict]
canonicalizeArrow arr =
  target arr
  |> ndEdges
  |> fmap dict
  |> fmap Map.elems
  |> canonicalizeGradedEqlistSet (dict arr !)
  |> fmap (base :)
  |> fmap ((`zip` [base..]) .> Map.fromList)

-- | Make a node with validation.
makeNode :: [Edge e] -> Maybe (Node e)
makeNode edges = guarded (root .> validate) (Node {edges = edges})

-- | Make an arrow with validation.
makeArrow :: Dict -> Node e -> Maybe (Arrow e)
makeArrow dict target = guarded validate (Arrow {dict = dict, target = target})

-- * Folding #folding#

-- | A value labeled by the relative position of the node.
data Located r = AtOuter | AtBoundary | AtInner r
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Retrieve a reachable value, or return nothing if it is unreachable.
fromReachable :: r -> Located r -> Maybe r
fromReachable _ AtOuter     = Nothing
fromReachable r AtBoundary  = Just r
fromReachable _ (AtInner r) = Just r

-- | Retrieve the inner variant of a located value, otherwise return nothing.
fromInner :: Located r -> Maybe r
fromInner (AtInner r) = Just r
fromInner _           = Nothing

-- | Fold a BAC.  All nodes are visited only once according to symbols.
--
--   Examples:
--
--   >>> fold (\_ results -> "<" ++ concat results ++ ">") cone
--   "<<<>><<<><>><<><>>>>"
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
--
--   Examples:
--
--   >>> foldUnder 6 (\_ results -> "<" ++ concat (mapMaybe fromInner results) ++ ">") cone
--   AtInner "<<<><>>>"
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

-- | Modify edges of BAC.
modify ::
  ((Arrow e, Edge e) -> Node e' -> [Edge e'])
              -- ^ The function to modify edge.  The first parameter is the original edge
              --   to modified, and the second parameter is the modified target node.  It
              --   should return a list of modified edges.
  -> Node e   -- ^ The root node of BAC to modify.
  -> Node e'  -- ^ The modified result.
modify f =
  fold \curr results -> Node do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | Modify edges of BAC under a node.
modifyUnder ::
  Symbol                -- ^ The symbol referencing to the boundary.
  -> ((Arrow e, Edge e) -> Located (Node e') -> [Edge e'])
                        -- ^ The modify function.  Where the results of child nodes are
                        --   labeled by `Located`.
  -> Node e             -- ^ The root node of BAC to modify.
  -> Located (Node e')  -- ^ The modified result, which is labeled by `Located`.
modifyUnder sym f =
  foldUnder sym \curr results -> Node do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | Map stored data of BAC.
map :: ((Arrow e, Arrow e) -> e -> o) -> Node e -> Node o
map f = modify \(curr, (value, arr)) res ->
  return (f (curr, arr) value, arr {target = res})

-- | Map stored data of BAC under a node.
mapUnder :: Symbol -> (Bool -> (Arrow e, Arrow e) -> e -> e) -> Node e -> Maybe (Node e)
mapUnder sym f node = do
  curr <- node |> arrow sym
  let res0 = target curr
  fromReachable res0 $ node |> modifyUnder sym \(curr, (value, arr)) -> \case
    AtOuter     -> return (value, arr)
    AtBoundary  -> return (f False (curr, arr) value, arr {target = res0})
    AtInner res -> return (f True (curr, arr) value, arr {target = res})

-- | Map and find nodes of BAC.
findMapNode :: (Arrow e -> Maybe a) -> Node e -> [a]
findMapNode f = Map.elems . fold \curr results ->
  results |> Map.unions |> case f curr of
    Just res -> Map.insert (symbol curr) res
    Nothing -> id

-- | Map and find nodes of BAC under a node.
findMapNodeUnder :: Symbol -> (Arrow e -> Maybe a) -> Node e -> Maybe [a]
findMapNodeUnder sym f =
  fromReachable [] . fmap Map.elems . foldUnder sym \curr results ->
    results |> mapMaybe fromInner |> Map.unions |> case f curr of
      Just res -> Map.insert (symbol curr) res
      Nothing -> id

-- | Map and find edges of BAC.
findMap :: ((Arrow e, Arrow e) -> e -> Maybe a) -> Node e -> [a]
findMap f = concat . Map.elems . fold \curr results ->
  results |> Map.unions |> Map.insert (symbol curr) do
    (value, arr) <- edges (target curr)
    toList $ f (curr, arr) value

-- | Map and find edges of BAC under a node.
findMapUnder ::
  Symbol -> (Bool -> (Arrow e, Arrow e) -> e -> Maybe a) -> Node e -> Maybe [a]
findMapUnder sym f =
  fromReachable [] . fmap (concat . Map.elems) . foldUnder sym \curr results ->
    results |> mapMaybe fromInner |> Map.unions |> Map.insert (symbol curr) do
      (res, (value, arr)) <- results `zip` edges (target curr)
      toList case res of
        AtOuter -> Nothing
        AtBoundary -> f False (curr, arr) value
        AtInner _ -> f True (curr, arr) value

-- * Non-Categorical Operations #operations#

{- |
Rewire edges of a given node.

Examples:

>>> printNode' $ fromJust $ rewireEdges 0 [((), 1), ((), 2), ((), 3)] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->2
  *0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1

>>> printNode' $ fromJust $ rewireEdges 3 [((), 1), ((), 4), ((), 3)] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
      &2
  - 0->4; 1->2; 2->3
    *1
  - 0->3
    *2

>>> rewireEdges 3 [((), 1), ((), 5), ((), 3)] cone
Nothing
-}
rewireEdges ::
  Symbol             -- ^ The symbol referencing to the node to rewire.
  -> [(e, Symbol)]   -- ^ The list of values and symbols of rewired edges.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
rewireEdges src tgts node = do
  src_arr <- node |> arrow src
  let src_edges = edges (target src_arr)
  src_edges' <- tgts |> traverse (traverse (`arrow` target src_arr))
  let res0 = Node src_edges'

  let nd_symbols = fmap (snd .> symbol) .> filter (nondecomposable (target src_arr))
  guard $ nd_symbols src_edges == nd_symbols src_edges'

  fromReachable res0 $ node |> modifyUnder src \(_, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {target = res0})

{- |
Relabel a given node.

Examples:

>>> let remap = fromList [(0,0), (1,4), (2,1), (3,2), (4,3)] :: Dict
>>> printNode' $ fromJust $ relabelObject 3 remap cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2; 2->6; 3->4; 4->4
  - 0->4; 1->1; 2->2
    &1
    - 0->1
      *0
    - 0->2
  - 0->3; 1->1; 2->2
    *1

>>> relabelObject 3 (fromList [(0,0), (1,4), (2,1), (3,2)]) cone
Nothing

>>> relabelObject 3 (fromList [(0,0), (1,4), (2,1), (3,2), (4,4)]) cone
Nothing

>>> relabelObject 3 (fromList [(0,3), (1,4), (2,1), (3,2), (4,0)]) cone
Nothing
-}
relabelObject ::
  Symbol             -- ^ The symbol referencing to the node to relabel.
  -> Dict            -- ^ The dictionary to relabel the symbols of the node.
  -> Node e          -- ^ The root node of BAC.
  -> Maybe (Node e)  -- ^ The result.
relabelObject tgt mapping node = do
  tgt_arr <- node |> arrow tgt
  guard $ base `Map.member` mapping && mapping ! base == base
  guard $ Map.keys mapping == symbols (target tgt_arr)
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  let res0 = Node do
        (value, arr) <- edges (target tgt_arr)
        return (value, arr {dict = mapping `cat` dict arr})
  fromReachable res0 $ node |> modifyUnder tgt \(_, (value, arr)) -> \case
    AtOuter -> return (value, arr)
    AtInner res -> return (value, arr {target = res})
    AtBoundary -> return (value, arr {dict = dict arr `cat` unmapping, target = res0})
