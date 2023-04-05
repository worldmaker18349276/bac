{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}

module BAC.Base (
  -- * Basic #basic#

  -- ** Types #types#
  -- | Tree representation of a bounded acyclic category.
  --
  --   A bounded acyclic category can be represented as a tree structure with implicitly
  --   shared nodes.
  --
  --   Edges of such structure have dictionaries, which obey three laws:
  --
  --   1.  __totality__: the dictionary of an edge should be a mapping from all valid symbols
  --       in the child node to valid symbols in the parent node.
  --   2.  __surjectivity__: all valid symbols should be covered by the dictionaries of
  --       outgoing edges, except the base symbol.
  --   3.  __supportivity__: if dictionaries of given two paths with the same starting node
  --       map the base symbol to the same symbol, then they should have the same dictionary
  --       and target node.  Note that null paths also count.
  --
  --   See my paper for a detailed explanation.

  Node (Node, edges),
  Edge,
  Arrow (Arrow, dict, target),
  Dict,
  Symbol,
  base,
  symbols,
  cat,

  -- ** Arrow #arrow#

  Location (..),
  arrows,
  arrowsND,
  root,
  join,
  divide,
  extend,
  locate,
  arrow,
  symbol,
  nondecomposable,

  -- ** Tuple of Arrows

  arrow2,
  symbol2,
  divide2,
  extend2,
  prefix,
  prefixND,
  suffix,
  suffixND,

  -- ** Validation #validation#

  validate,
  validateAll,
  makeNode,
  makeArrow,

  -- * Isomorphism #isomorphism#

  eqStruct,
  canonicalize,
  canonicalizeObject,

  -- * Folding #folding#

  Located (..),
  fromReachable,
  fromInner,
  fold,
  fold',
  foldUnder,
  foldND,
  foldUnderND,
  modify,
  modifyUnder,
  map,
  mapUnder,
  arrowsOrd,
  arrowsOrdUnder,

  -- * Non-Categorical Operations #operations#

  rewireEdges,
  relabelObject,
) where

import Control.Monad (guard)
import Control.Monad.ST (runST, fixST)
import Data.Bifunctor (bimap, Bifunctor (second))
import Data.List.Extra (groupSortOn, nubSort, allSame, nubSortOn)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe, fromMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (dupe)
import Data.Functor (void)
import Numeric.Natural (Natural)
import GHC.Stack (HasCallStack)
import Prelude hiding (map)

import Utils.Memoize (unsafeMemoizeWithKey, memoizeWithKey)
import Utils.Utils ((.>), (|>), guarded, mergeNubOn)
import Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet)

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Map (fromList, elems)

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
symbols = arrows .> concatMap (dict .> Map.elems) .> (base :) .> nubSort

-- | Concatenate two dictionaries:
--
--   > (a `cat` b) ! i = a ! (b ! i)
--
--   It may crash if given dictionaries are not composable.
cat :: HasCallStack => Dict -> Dict -> Dict
cat = fmap . (!)

-- | The relative location between nodes.
data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

-- | Arrows representing the edges of a node.
arrows :: Node e -> [Arrow e]
arrows = edges .> fmap snd

-- | Nondecomposable arrows representing the edges of a node.
arrowsND :: Node e -> [Arrow e]
arrowsND node =
  node
  |> arrows
  |> filter (symbol .> nondecomposable node)
  |> nubSortOn symbol

-- | Root arrow of a node.
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
  |> fmap (arrow (target arr12) .> fromJust)

-- | Extend an arrow by joining to the edges of the target node.
extend :: Arrow e -> [Arrow e]
extend arr = target arr |> arrows |> fmap (join arr)

-- | Find the relative Location of the node referenced by the given symbol with respect to
--   a given arrow.
--
--   Examples:
--
--   >>> locate (root cone) 2
--   Inner
--
--   >>> locate (root cone) 0
--   Boundary
--
--   >>> locate (root cone) 5
--   Outer
locate :: Arrow e -> Symbol -> Location
locate arr sym
  | symbol arr == sym   = Boundary
  | sym `elem` dict arr = Inner
  | otherwise           = Outer

-- | Make a arrow pointing to the node referenced by the given symbol.
--   Return `Nothing` if it is outside the node.
--
--   Examples:
--
--   >>> arrow cone 3
--   Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
--
--   >>> arrow cone 5
--   Nothing
arrow :: Node e -> Symbol -> Maybe (Arrow e)
arrow node sym = go (root node)
  where
  go arr = case locate arr sym of
    Outer    -> Nothing
    Boundary -> Just arr
    Inner    -> Just $ arr |> extend |> mapMaybe go |> head

-- | Find the symbol referencing to the given arrow.
--   It is the inverse of `arrow`:
--
--   > fmap symbol (arrow node sym) = Just sym
--
--   Examples:
--
--   >>> fmap symbol (arrow cone 3)
--   Just 3
--
--   >>> fmap symbol (arrow cone 5)
--   Nothing
symbol :: Arrow e -> Symbol
symbol = dict .> (! base)

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
  (locate (root node) sym |> (/= Outer))
  && (node |> arrows |> all ((`locate` sym) .> (/= Inner)))

-- | Make a 2-chain by given pair of symbols.
--
--   Examples:
--
--   >>> fmap fst (arrow2 cone (3,2))
--   Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
--
--   >>> fmap snd (arrow2 cone (3,2))
--   Just (Arrow {dict = fromList [(0,2)], target = ...
--
--   >>> arrow2 cone (1,2)
--   Nothing
arrow2 :: Node e -> (Symbol, Symbol) -> Maybe (Arrow e, Arrow e)
arrow2 node (src, tgt) = do
  src_arr <- arrow node src
  tgt_subarr <- arrow (target src_arr) tgt
  return (src_arr, tgt_subarr)

-- | Find the pair of symbols referencing to the given 2-chain.
--   It is the inverse of `arrow2`:
--
--   > fmap symbol2 (arrow2 node sym2) = Just sym2
--
--   Examples:
--
--   >>> fmap symbol2 (arrow2 cone (3,2))
--   Just (3,2)
--
--   >>> fmap symbol2 (arrow2 cone (1,2))
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
  target arr1
  |> arrows
  |> filter ((`locate` symbol arr2) .> (/= Outer))
  |> concatMap (\arr -> arr `divide` arr2 |> fmap (arr1 `join` arr,))

-- | Find prefix edges of paths from a node to a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` prefix node sym
--   > ->  symbol (arr1 `join` arr2) == sym
--   > &&  (_, arr1) `elem` edges node
prefix :: Node e -> Symbol -> [(Arrow e, Arrow e)]
prefix node sym =
  arrow node sym
  |> maybe [] \tgt_arr ->
    node
    |> arrows
    |> concatMap (\arr -> divide arr tgt_arr |> fmap (arr,))

prefixND :: Node e -> Symbol -> [(Arrow e, Arrow e)]
prefixND node sym =
  prefix node sym
  |> filter (\(arr1, _) -> nondecomposable node (symbol arr1))
  |> nubSortOn symbol2

-- | Find suffix edges of paths from a node to a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` suffix node sym
--   > ->  symbol (arr1 `join` arr2) == sym
--   > &&  (_, arr2) `elem` edges (target arr1)
suffix :: Node e -> Symbol -> [(Arrow e, Arrow e)]
suffix node sym =
  node
  |> arrowsOrdUnder sym
  |> fromMaybe []
  |> concatMap \curr ->
    curr
    |> target
    |> arrows
    |> filter (join curr .> symbol .> (== sym))
    |> fmap (curr,)
  

suffixND :: Node e -> Symbol -> [(Arrow e, Arrow e)]
suffixND node sym =
  suffix node sym
  |> filter (\(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))
  |> nubSortOn symbol2

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
  descendants node = symbols node |> fmap (arrow node) |> fmap fromJust

-- | Check if an arrow is valid in depth.  All descendant nodes will be checked.
--
--   Examples:
--
--   >>> validateAll $ root cone
--   True
--
--   >>> validateAll $ root torus
--   True
--
--   >>> validateAll $ root crescent
--   True
--
--   >>> validateAll $ fromJust $ arrow cone 3
--   True
validateAll :: Arrow e -> Bool
validateAll arr = validateChildren && validate arr
  where
  validateChildren = target arr |> arrows |> all validateAll

-- | Make a node with validation.
makeNode :: [Edge e] -> Maybe (Node e)
makeNode edges = guarded (root .> validate) (Node {edges = edges})

-- | Make an arrow with validation.
makeArrow :: Dict -> Node e -> Maybe (Arrow e)
makeArrow dict target = guarded validate (Arrow {dict = dict, target = target})

-- | Structural equality, the equality of nodes up to rewiring.
--   The symbols of nodes should be the same, and equality of child nodes are not checked.
--   The node with the same structure can be unioned by merging their edges.
eqStruct :: [Node e] -> Bool
eqStruct = fmap arrowsND .> fmap (fmap dict) .> allSame

-- | Find mappings to canonicalize the order of symbols of a node.  It will return
--   multiple mappings if it possesses some symmetries.
--   The absolute order has no meaning, but can be used to check the isomorphism between
--   nodes.  The relative order between these mappings forms automorphism of this BAC.
--
--   Examples:
--
--   >>> fmap elems $ canonicalize crescent
--   [[0,1,2,3,4]]
--
--   >>> fmap elems $ canonicalize $ target $ fromJust $ arrow crescent 1
--   [[0,1,2,3,4,5,6],[0,1,2,3,6,5,4],[0,3,2,1,4,5,6],[0,3,2,1,6,5,4],[0,4,5,6,1,2,3],[0,6,5,4,1,2,3],[0,4,5,6,3,2,1],[0,6,5,4,3,2,1]]
canonicalize :: Node e -> [Dict]
canonicalize =
  arrowsND
  .> fmap dict
  .> fmap Map.elems
  .> canonicalizeEqlistSet
  .> fmap (base :)
  .> fmap ((`zip` [base..]) .> Map.fromList)

-- | Find mappings to canonicalize the order of symbols of a subnode specified by given
--   symbol.  The induced automorphisms are invariant under the mapping of incoming edges.
--   It can be used to check the upper isomorphism between objects.
--
--   Examples:
--
--   >>> fmap elems $ fromJust $ canonicalizeObject crescent 1
--   [[0,1,2,5,3,4,6],[0,3,4,6,1,2,5]]
canonicalizeObject :: Node e -> Symbol -> Maybe [Dict]
canonicalizeObject node tgt = do
  guard $ tgt /= base
  tgt_arr <- arrow node tgt
  let keys =
        tgt
        |> suffixND node
        |> fmap (snd .> dict .> fmap (: []))
        |> foldl (Map.unionWith (++)) Map.empty
  return $
    target tgt_arr
    |> arrowsND
    |> fmap dict
    |> fmap Map.elems
    |> canonicalizeGradedEqlistSet (keys !)
    |> fmap (base :)
    |> fmap ((`zip` [base..]) .> Map.fromList)

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
fold f node = node |> root |> go
  where
  go = memoize \curr -> curr |> extend |> fmap go |> f curr
  memoize = unsafeMemoizeWithKey symbol

-- | Safe version of fold.
--
--   Examples:
--
--   >>> fold' (\_ results -> "<" ++ concat results ++ ">") cone
--   "<<<>><<<><>><<><>>>>"
fold' :: (Arrow e -> [c] -> c) -> Node e -> c
fold' f node = runST do go' <- go; node |> root |> go'
  where
  go = fixST \go' -> memoizeWithKey symbol \curr ->
    curr |> extend |> traverse go' |> fmap (f curr)

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
  f' curr results = case locate curr sym of
    Outer    -> AtOuter
    Boundary -> AtBoundary
    Inner    -> AtInner $ f curr results

foldND ::
  (Arrow e -> [r] -> r)  -- ^ The function to reduce a node and the results from its child
                         --   nodes into a value.
  -> Node e              -- ^ The root node of BAC to fold.
  -> r                   -- ^ The folding result.
foldND f = fold \curr results ->
  results `zip` arrows (target curr)
  |> filter (snd .> symbol .> nondecomposable (target curr))
  |> fmap fst
  |> f curr

foldUnderND ::
  Symbol                            -- ^ The symbol referencing to the boundary.
  -> (Arrow e -> [Located r] -> r)  -- ^ The reduce function.  Where the results of child
                                    --   nodes are labeled by `Located`.
  -> Node e                         -- ^ The root node of BAC to fold.
  -> Located r                      -- ^ The folding result, which is labeled by `Located`.
foldUnderND sym f = foldND f'
  where
  f' curr results = case locate curr sym of
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
  curr <- arrow node sym
  let res0 = target curr
  fromReachable res0 $ node |> modifyUnder sym \(curr, (value, arr)) -> \case
    AtOuter     -> return (value, arr)
    AtBoundary  -> return (f False (curr, arr) value, arr {target = res0})
    AtInner res -> return (f True (curr, arr) value, arr {target = res})

-- | Find all arrows of this node in descending order.
--
--   Examples:
--
--   >>> fmap symbol $ arrowsOrd cone
--   [2,1,6,4,3,0]
arrowsOrd :: Node e -> [Arrow e]
arrowsOrd = fmap snd . foldND \curr results ->
  results ++ [[(symbol curr, curr)]] |> mergeNubOn fst

-- | Find all arrows under a given symbol of this node in descending order.
--
--   Examples:
--
--   >>> fmap symbol $ fromJust $ arrowsOrdUnder 6 cone
--   [4,3,0]
arrowsOrdUnder :: Symbol -> Node e -> Maybe [Arrow e]
arrowsOrdUnder sym =
  fromReachable [] . fmap (fmap snd) . foldUnderND sym \curr results ->
    results |> mapMaybe fromInner |> (++ [[(symbol curr, curr)]]) |> mergeNubOn fst

{- |
Rewire edges of a given node.

Examples:

>>> printNode' $ fromJust $ rewireEdges 0 [((), 1), ((), 4), ((), 3)] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  &1
  - 0->1
    *0
  - 0->2
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    *1
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
  src_arr <- arrow node src
  let nd_syms = target src_arr |> arrowsND |> fmap symbol
  src_edges' <- tgts |> traverse (traverse (arrow (target src_arr)))
  let res0 = Node src_edges'

  let nd_syms' = res0 |> arrowsND |> fmap symbol
  guard $ nd_syms == nd_syms'

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
  tgt_arr <- arrow node tgt
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
