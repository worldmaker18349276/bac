{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

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
  --   1.  __totality__: the dictionary of an edge should be a mapping from all valid
  --       symbols on the child node to valid symbols on the parent node.
  --   2.  __surjectivity__: all valid symbols should be covered by the dictionaries of
  --       outgoing edges, except the base symbol.
  --   3.  __supportivity__: if dictionaries of given two paths with the same starting
  --       node map the base symbol to the same symbol, then they should have the same
  --       dictionary and target node.
  --
  --   They can be translated into following codes:
  --
  --   > forall edge.  sort $ Map.keys $ dict edge  =  symbols $ target edge
  --
  --   > forall node.  nubSort $ concatMap (Map.values . dict) $ edges node  =  filter (/= base) $ symbols node
  --
  --   > forall path1 path2.
  --   >   foldl1 (cat `on` dict) path1 ! base = foldl1 (cat `on` dict) path2 ! base
  --   >   ->  ( foldl1 (cat `on` dict) path1 = foldl1 (cat `on` dict) path2
  --   >       ,          target $ last path1 =          target $ last path2
  --   >       )
  --
  --   See my paper for a detailed explanation.

  BAC (BAC),
  edges,
  Arrow (..),
  Dict,
  Symbol,
  base,
  symbols,
  cat,
  empty,
  singleton,

  -- ** Validation #validation#

  validate,
  validateArrow,
  validateAll,
  makeBAC,
  makeArrow,

  -- * Arrows #arrows#

  -- ** Single Arrow #arrow#

  root,
  join,
  arrow,
  path,
  symbol,
  extend,
  inv,
  divide,
  arrows,
  paths,
  arrowsUnder,
  pathsUnder,

  -- ** Pair of Arrows #arrow2#

  arrow2,
  symbol2,
  extend2,
  divide2,
  prefix,
  suffix,

  -- ** Relation #relation#

  Location (..),
  locate,
  compare,
  nondecomposable,
  edgesND,
  prefixND,
  suffixND,

  -- * Folding #folding#

  Located (..),
  fromReachable,
  fromInner,
  fold,
  foldUnder,
  modify,
  modifyUnder,
  cofold,
  cofoldUnder,
) where

import Data.Bifunctor (bimap)
import Data.Foldable (foldl')
import Data.List (sortOn)
import Data.List.Extra (allSame, groupSortOn, nubSort, snoc)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Tuple.Extra (dupe)
import GHC.Stack (HasCallStack)
import Numeric.Natural (Natural)
import Prelude hiding (compare, map)

import Utils.Memoize (memoizeWithKey)
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import BAC
-- >>> import BAC.Examples (cone, torus, crescent)

-- | The tree representation of a bounded acyclic category.
--   It should be validated by `validate`.
newtype BAC e = BAC { edges :: [Arrow e] } deriving (Eq, Ord, Show, Functor)

-- | Arrow to a bounded acyclic category, representing a downward functor.
--   It should be validated by `validateArrow`, or use `makeArrow`.
data Arrow e = Arrow {dict :: Dict, value :: e, target :: BAC e} deriving (Eq, Ord, Show, Functor)

-- | Dictionary of an arrow, representing mapping of objects between nodes.
type Dict = Map Symbol Symbol

-- | Symbol of a node, representing an object of the corresponding category.
type Symbol = Natural

-- | The base symbol, representing an initial object.
base :: Symbol
base = 0

{- |
All symbols of a node.  The first one is the base symbol.

Examples:

>>> symbols cone
[0,1,2,3,4,6]

>>> symbols torus
[0,1,2,3,5]

>>> symbols crescent
[0,1,2,3,4]
-}
symbols :: BAC e -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> (base :) .> nubSort

{- |
Concatenate two dictionaries:

> (a `cat` b) ! i = a ! (b ! i)

It may crash if given dictionaries are not composable.
-}
cat :: HasCallStack => Dict -> Dict -> Dict
cat = fmap . (!)

{- |
A node without descendant (a BAC without proper object).

Examples:

>>> printBAC empty
-}
empty :: BAC e
empty = BAC []

{- |
a node with only one descendant (a BAC with only one proper object).

Examples:

>>> printBAC $ fromJust $ singleton 1
- 0->1

>>> printBAC $ fromJust $ singleton 2
- 0->2
-}
singleton :: Symbol -> e -> Maybe (BAC e)
singleton sym e = if sym == base then Nothing else Just $ BAC [new_edge]
  where
  new_dict = Map.singleton base sym
  new_node = empty
  new_edge = Arrow {dict = new_dict, value = e, target = new_node}

-- | Root arrow of a node.
root :: Monoid e => BAC e -> Arrow e
root node = Arrow {dict = id_dict, value = mempty, target = node}
  where
  id_dict = node |> symbols |> fmap dupe |> Map.fromList

-- | Join two arrows into one arrow.
--   It may crashes if two arrows are not composable.
join :: (HasCallStack, Monoid e) => Arrow e -> Arrow e -> Arrow e
join arr1 arr2 = arr2 {dict = dict arr1 `cat` dict arr2, value = value arr1 <> value arr2}

inv :: Dict -> Symbol -> [Symbol]
inv dict sym =
  dict
  |> Map.toList
  |> filter (snd .> (== sym))
  |> fmap fst
  |> nubSort

-- | Divide two arrows.  The first is divisor and the second is the dividend, and they
--   should start at the same node.
--   It obeys the following law:
--
--   > arr23 `elem` divide arr12 arr13  ->  arr12 `join` arr23 == arr13
divide :: Monoid e => Arrow e -> Arrow e -> [Arrow e]
divide arr12 arr13 =
  inv (dict arr12) (symbol arr13)
  |> fmap (arrow (target arr12) .> fromJust)

-- | Extend an arrow by joining to the edges of the target node.
extend :: Monoid e => Arrow e -> [Arrow e]
extend arr = target arr |> edges |> fmap (join arr)

-- | The relative location between nodes.
data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

{- |
Relative location of the node referenced by the given symbol with respect to a given arrow.

Examples:

>>> locate (root cone) 2
Inner

>>> locate (root cone) 0
Boundary

>>> locate (root cone) 5
Outer
-}
locate :: Arrow e -> Symbol -> Location
locate arr sym
  | symbol arr == sym   = Boundary
  | sym `elem` dict arr = Inner
  | otherwise           = Outer

{- |
Partial order between two arrows.  They should start at the same node.
It crashes with inconsistencies caused by bad data.

Examples:

>>>  fromJust (arrow cone 4) `compare` fromJust (arrow cone 6)
Just LT

>>>  fromJust (arrow cone 4) `compare` fromJust (arrow cone 4)
Just EQ

>>> fromJust (arrow cone 2) `compare` fromJust (arrow cone 6)
Nothing
-}
compare :: HasCallStack => Arrow e -> Arrow e -> Maybe Ordering
compare arr1 arr2 =
  case (locate arr1 (symbol arr2), locate arr2 (symbol arr1)) of
    (Boundary, Boundary) -> Just EQ
    (Inner, Outer) -> Just LT
    (Outer, Inner) -> Just GT
    (Outer, Outer) -> Nothing
    _ -> error "invalid state"

{- |
An arrow to the node referenced by the given symbol, or `Nothing` if it is outside the
node.

Examples:

>>> arrow cone 3
Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...

>>> arrow cone 5
Nothing
-}
arrow :: Monoid e => BAC e -> Symbol -> Maybe (Arrow e)
arrow node sym = go (root node)
  where
  go arr = case locate arr sym of
    Outer    -> Nothing
    Boundary -> Just arr
    Inner    -> Just $ arr |> extend |> mapMaybe go |> head

path :: Monoid e => BAC e -> Symbol -> [Arrow e]
path node sym = go (root node)
  where
  go arr = case locate arr sym of
    Outer    -> []
    Boundary -> [arr]
    Inner    -> arr |> extend |> concatMap go

{- |
The symbol referencing to the given arrow.
It is the inverse of `arrow`:

Examples:

>>> fmap symbol (arrow cone 3)
Just 3

>>> fmap symbol (arrow cone 5)
Nothing
-}
symbol :: Arrow e -> Symbol
symbol = dict .> (! base)

{- |
A 2-chain referenced by the given pair of symbols.

Examples:

>>> fmap fst (arrow2 cone (3,2))
Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...

>>> fmap snd (arrow2 cone (3,2))
Just (Arrow {dict = fromList [(0,2)], target = ...

>>> arrow2 cone (1,2)
Nothing
-}
arrow2 :: Monoid e => BAC e -> (Symbol, Symbol) -> Maybe (Arrow e, Arrow e)
arrow2 node (src, tgt) = do
  src_arr <- arrow node src
  tgt_subarr <- arrow (target src_arr) tgt
  return (src_arr, tgt_subarr)

{- |
The pair of symbols referencing the given 2-chain.
It is the inverse of `arrow2`.

Examples:

>>> fmap symbol2 (arrow2 cone (3,2))
Just (3,2)

>>> fmap symbol2 (arrow2 cone (1,2))
Nothing
-}
symbol2 :: (Arrow e, Arrow e) -> (Symbol, Symbol)
symbol2 = symbol `bimap` symbol

{- |
Find prefix edges of paths from a node to a given symbol.
It obeys the following law:

> (arr1, arr2) `elem` prefix node sym
> ->  arr1 `elem` edges node
> &&  symbol (arr1 `join` arr2) == sym
-}
prefix :: Monoid e => BAC e -> Symbol -> [(Arrow e, Arrow e)]
prefix node sym =
  arrow node sym
  |> maybe [] \tgt_arr ->
    node
    |> edges
    |> concatMap \edge ->
      divide edge tgt_arr
      |> fmap (edge,)

{- |
Find suffix edges of paths from a node to a given symbol.
It obeys the following law:

> (arr1, arr2) `elem` suffix node sym
> ->  arr2 `elem` edges (target arr1)
> &&  symbol (arr1 `join` arr2) == sym
-}
suffix :: Monoid e => BAC e -> Symbol -> [(Arrow e, Arrow e)]
suffix node sym =
  arrowsUnder node sym
  |> sortOn symbol
  |> concatMap \curr ->
    curr
    |> target
    |> edges
    |> filter (join curr .> symbol .> (== sym))
    |> fmap (curr,)

{- |
Extend a tuple of arrows.
It obeys the following law:

> (arr13, arr34) `elem` extend2 (arr12, arr24)
> ->  arr13 `elem` extend arr12
> &&  arr12 `join` arr24 == arr13 `join` arr34
-}
extend2 :: Monoid e => (Arrow e, Arrow e) -> [(Arrow e, Arrow e)]
extend2 (arr1, arr2) =
  target arr1
  |> edges
  |> filter ((`locate` symbol arr2) .> (/= Outer))
  |> concatMap \edge ->
    edge `divide` arr2
    |> fmap (arr1 `join` edge,)

{- |
Divide two tuples of arrows.  The first is divisor and the second is the dividend, and
they should start and end at the same node.
It obeys the following laws:

> arr12 `join` arr24  ==  arr13 `join` arr34
> &&  arr23 `elem` divide2 (arr12, arr24) (arr13, arr34)
> ->  arr12 `join` arr23 == arr13
> &&  arr23 `join` arr34 == arr34
-}
divide2 :: Monoid e => (Arrow e, Arrow e) -> (Arrow e, Arrow e) -> [Arrow e]
divide2 (arr12, arr24) (arr13, arr34) =
  arr12 `divide` arr13 |> filter \arr23 ->
    symbol (arr23 `join` arr34) == symbol arr24


{- |
Check if the given symbol reference a nondecomposable arrow, which represent a
nondecomposable initial morphism.
The nondecomposable arrow is an arrow which cannot be written as a concatenation of
multiple proper arrows.

Examples:

>>> nondecomposable cone 3  -- a nondecomposable proper arrow
True

>>> nondecomposable cone 4  -- a decomposable proper arrow
False

>>> nondecomposable cone 0  -- a null arrow
True

>>> nondecomposable cone 10  -- no such arrow
True
-}
nondecomposable :: BAC e -> Symbol -> Bool
nondecomposable node sym = node |> edges |> all ((`locate` sym) .> (/= Inner))

-- | Nondecomposable edges of a node.
edgesND :: BAC e -> [Arrow e]
edgesND node =
  edges node
  |> filter (symbol .> nondecomposable node)

-- | Find nondecomposible prefix edges of paths from a node to a given symbol.
--   See `prefix`.
prefixND :: Monoid e => BAC e -> Symbol -> [(Arrow e, Arrow e)]
prefixND node sym =
  prefix node sym
  |> filter (\(arr1, _) -> nondecomposable node (symbol arr1))

-- | Find nondecomposible suffix edges of paths from a node to a given symbol.
--   See `suffix`.
suffixND :: Monoid e => BAC e -> Symbol -> [(Arrow e, Arrow e)]
suffixND node sym =
  suffix node sym
  |> filter (\(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))


-- | Check if a node is valid.  All child nodes of this node are assumed to be valid.
--   See [Types]("BAC.Base#g:types") for detail.
validate :: (Monoid e, Eq e) => BAC e -> Bool
validate node = validateDicts && validateSup
  where
  -- check totality for all edges of this node.
  validateDicts = edges node |> all \edge -> Map.keys (dict edge) == symbols (target edge)
  -- check supportivity for all paths started at this node.
  validateSup =
    edges node
    |> concatMap (\edge -> edge |> target |> arrows |> fmap (join edge))
    |> (root node :)
    |> groupSortOn symbol
    |> fmap (fmap \arr -> (dict arr, target arr))
    |> all allSame

-- | Check if an arrow is valid.  The target node is assumed to be valid.
--   See [Types]("BAC.Base#g:types") for detail.
validateArrow :: (Monoid e, Eq e) => Arrow e -> Bool
validateArrow arr = validateDict && validateSup
  where
  -- check totality for this arrow.
  validateDict = Map.keys (dict arr) == symbols (target arr)
  -- check supportivity for all paths prefixed with this arrow.
  validateSup =
    arr
    |> target
    |> arrows
    |> fmap (join arr)
    |> (arr :)
    |> groupSortOn symbol
    |> fmap (fmap \subarr -> (dict subarr, target subarr))
    |> all allSame

{- |
Check if an arrow is valid in depth.  All descendant nodes will be checked.

Examples:

>>> validateAll cone
True

>>> validateAll torus
True

>>> validateAll crescent
True
-}
validateAll :: (Monoid e, Eq e) => BAC e -> Bool
validateAll node = validateChildren && validate node
  where
  validateChildren = node |> edges |> all (target .> validateAll)

-- | Make a node with validation.
makeBAC :: (Monoid e, Eq e) => [Arrow e] -> Maybe (BAC e)
makeBAC = BAC .> guarded validate

-- | Make an arrow with validation.
makeArrow :: (Monoid e, Eq e) => Dict -> e -> BAC e -> Maybe (Arrow e)
makeArrow dict e target = Arrow {dict = dict, value = e, target = target} |> guarded validateArrow


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

{- |
Fold a BAC.  All nodes are visited only once according to symbols.

Examples:

>>> fold (\curr results -> concat results `snoc` symbol curr) cone
[2,1,2,6,4,2,6,4,3,0]

>>> fold (\curr results -> concat results `snoc` symbol curr) crescent
[3,2,3,4,3,2,3,4,1,0]

>>> fold (\curr results -> concat results `snoc` symbol curr) torus
[3,3,2,3,3,5,3,3,2,3,3,5,1,0]

The evaluation order follows the DFS algorithm.  Each node will only be evaluated once.

>>> import Debug.Trace (traceShow)
>>> fold (\curr results -> results == results `seq` traceShow (symbol curr) ()) torus `seq` return ()
3
2
5
1
0
-}
fold ::
  Monoid e
  => (Arrow e -> [r] -> r)
  -- ^ The function to reduce a node and the results into a value, where the results are
  --   reduced values of its child nodes.
  -> BAC e
  -- ^ The root node of BAC to fold.
  -> r
  -- ^ The folding result.
fold f = root .> memoizeWithKey symbol \self curr -> do
  res <- curr |> extend |> traverse self
  return $ f curr res

{- |
Fold a BAC under a node.

Examples:

>>> foldUnder 6 (\_ results -> "<" ++ concat (mapMaybe fromInner results) ++ ">") cone
AtInner "<<<><>>>"

>>> foldUnder 6 (\curr results -> concat (mapMaybe fromInner results) `snoc` symbol curr) cone
AtInner [4,4,3,0]

The evaluation order follows the DFS algorithm.

>>> import Debug.Trace (traceShow)
>>> res = foldUnder 6 (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
>>> res == res `seq` return ()
4
3
0
-}
foldUnder ::
  Monoid e
  => Symbol
  -- ^ The symbol referencing to the boundary.
  -> (Arrow e -> [Located r] -> r)
  -- ^ The reduce function.  Where the results of child nodes are labeled by `Located`.
  -> BAC e
  -- ^ The root node of BAC to fold.
  -> Located r
  -- ^ The folding result, which is labeled by `Located`.
foldUnder sym f = root .> memoizeWithKey symbol \self curr ->
  case locate curr sym of
    Outer    -> return AtOuter
    Boundary -> return AtBoundary
    Inner    -> do
      res <- curr |> extend |> traverse self
      return $ AtInner (f curr res)

-- | Modify edges of BAC.
modify ::
  Monoid e
  => ((Arrow e, Arrow e) -> BAC e -> [Arrow e])
  -- ^ The function to modify edge.  The first parameter is the original edge to modified,
  --   and the second parameter is the modified target node.  It should return a list of
  --   modified edges.
  -> BAC e
  -- ^ The root node of BAC to modify.
  -> BAC e
  -- ^ The modified result.
modify f =
  fold \curr results -> BAC do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | Modify edges of BAC under a node.
modifyUnder ::
  Monoid e
  => Symbol
  -- ^ The symbol referencing to the boundary.
  -> ((Arrow e, Arrow e) -> Located (BAC e) -> [Arrow e])
  -- ^ The modify function.  Where the results of child nodes are labeled by `Located`.
  -> BAC e
  -- ^ The root node of BAC to modify.
  -> Located (BAC e)
  -- ^ The modified result, which is labeled by `Located`.
modifyUnder sym f =
  foldUnder sym \curr results -> BAC do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

{- |
All arrows of this node in evalution order of fold.
It is equivalent to @fold (\curr results -> concat results `snoc` curr) .> nubOn symbol@.

Examples:

>>> fmap symbol $ arrows cone
[2,1,6,4,3,0]

>>> fmap symbol $ arrows crescent
[3,2,4,1,0]

>>> fmap symbol $ arrows torus
[3,2,5,1,0]
-}
arrows :: Monoid e => BAC e -> [Arrow e]
arrows = root .> go [] .> fmap snd
  where
  go res curr
    | sym `elem` fmap fst res = res
    | otherwise               = curr |> extend |> foldl' go res |> (`snoc` (sym, curr))
    where
    sym = symbol curr

paths :: Monoid e => BAC e -> [Arrow e]
paths = root .> go []
  where
  go res curr = curr |> extend |> foldl' go res |> (`snoc` curr)

{- |
All arrows under a given symbol of this node in evalution order of foldUnder.

Examples:

>>> fmap symbol $ arrowsUnder cone 6
[4,3,0]

>>> fmap symbol $ arrowsUnder cone 5
[]
-}
arrowsUnder :: Monoid e => BAC e -> Symbol -> [Arrow e]
arrowsUnder node sym = node |> root |> go [] |> fmap snd
  where
  go res curr
    | locate curr sym /= Inner = res
    | sym' `elem` fmap fst res = res
    | otherwise                = curr |> extend |> foldl' go res |> (`snoc` (sym', curr))
    where
    sym' = symbol curr

pathsUnder :: Monoid e => BAC e -> Symbol -> [Arrow e]
pathsUnder node sym = node |> root |> go []
  where
  go res curr
    | locate curr sym /= Inner = res
    | otherwise                = curr |> extend |> foldl' go res |> (`snoc` curr)

{- |
Fold a BAC reversely.

Examples:

>>> import Data.Bifunctor (first)
>>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) cone
[(6,[0,3,0,3,4,6]),(2,[0,1,0,3,0,3,4,2])]

>>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) crescent
[(3,[0,1,0,1,2,0,1,0,1,4,3])]

>>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) torus
[(3,[0,1,0,1,2,0,1,0,1,2,0,1,0,1,5,0,1,0,1,5,3])]

>>> import Debug.Trace (traceShow)
>>> res = cofold (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
>>> res == res `seq` return ()
0
3
4
6
1
2
-}
cofold :: Monoid e => (Arrow e -> [((Arrow e, Arrow e), r)] -> r) -> BAC e -> [(Arrow e, r)]
cofold f node = go [(root node, [])] []
  where
  -- go :: [(Arrow, [((Arrow, Arrow), r)])] -> [(Arrow, r)] -> [(Arrow, r)]
  go [] results = results
  go ((curr, args) : table) results = go table' results'
    where
    value = f curr args
    results' = if null (extend curr) then (curr, value) : results else results
    table' =
      edges (target curr)
      |> fmap (\edge -> (curr `join` edge, ((curr, edge), value)))
      |> foldl' insertSlot table
  -- insertSlot ::
  --   [(Arrow, [((Arrow, Arrow), r)])]
  --   -> (Arrow, ((Arrow, Arrow), r))
  --   -> [(Arrow, [((Arrow, Arrow), r)])]
  insertSlot [] (curr, arg) = [(curr, [arg])]
  insertSlot ((arr, args) : table) (curr, arg) =
    case locate curr (symbol arr) of
      Outer -> (arr, args) : insertSlot table (curr, arg)
      Boundary -> (arr, args `snoc` arg) : table
      Inner -> (curr, [arg]) : (arr, args) : table


{- |
Fold a BAC reversely under a node.

Examples:

>>> cofoldUnder 6 (\curr results -> concatMap snd results `snoc` symbol curr) cone
Just [0,3,0,3,4,6]

>>> import Debug.Trace (traceShow)
>>> res = cofoldUnder 6 (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
>>> res == res `seq` return ()
0
3
4
6
-}
cofoldUnder :: Monoid e => Symbol -> (Arrow e -> [((Arrow e, Arrow e), r)] -> r) -> BAC e -> Maybe r
cofoldUnder tgt f node =
  if locate (root node) tgt == Outer then Nothing else Just $ go [(root node, [])]
  where
  -- go :: [(Arrow, [((Arrow, Arrow), r)])] -> r
  go [] = error "invalid state"
  go ((curr, args) : table) = if symbol curr == tgt then value else go table'
    where
    value = f curr args
    table' =
      edges (target curr)
      |> fmap (\edge -> (curr `join` edge, ((curr, edge), value)))
      |> filter (fst .> (`locate` tgt) .> (/= Outer))
      |> foldl' insertSlot table
  -- insertSlot ::
  --   [(Arrow, [((Arrow, Arrow), r)])]
  --   -> (Arrow, ((Arrow, Arrow), r))
  --   -> [(Arrow, [((Arrow, Arrow), r)])]
  insertSlot [] (curr, arg) = [(curr, [arg])]
  insertSlot ((arr, args) : table) (curr, arg) =
    case locate curr (symbol arr) of
      Outer -> (arr, args) : insertSlot table (curr, arg)
      Boundary -> (arr, args `snoc` arg) : table
      Inner -> (curr, [arg]) : (arr, args) : table
