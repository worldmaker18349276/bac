{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}
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

  Tree (..),
  showTree,
  BAC,
  edges,
  fromEdges,
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
  validateAll,
  makeBAC,
  makeArrow,

  -- * Arrows #arrows#

  -- ** Single Arrow #arrow#

  root,
  join,
  arrow,
  symbol,
  extend,
  divide,
  arrows,
  arrowsUnder,

  -- ** Pair of Arrows #arrow2#

  arrow2,
  symbol2,
  extend2,
  divide2,
  prefix,
  suffix,
  allSuffix,

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

import Data.Bifunctor (Bifunctor (second), bimap)
import Data.Foldable (Foldable (foldl'))
import Data.List (sortOn, intercalate)
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
-- >>> import Data.Bifunctor (first)

-- | A tree whose edges are indexed by keys.
newtype Tree e = Tree (Map e (Tree e)) deriving (Eq, Ord, Show)

-- | Show tree concisely.
showTree :: Show e => Tree e -> String
showTree (Tree m) =
  m
  |> Map.toList
  |> fmap (\(key, subnode) -> show key ++ ":" ++ showTree subnode)
  |> intercalate ","
  |> (\c -> "{" ++ c ++ "}")

-- | The tree representation of a bounded acyclic category.
--   It should be validated by @validate . root@.
type BAC = Tree Dict

-- | The edges of a node.
edges :: BAC -> [Arrow]
edges (Tree m) = m |> Map.toList |> fmap (uncurry Arrow)

-- | Construct a BAC by edges.  The structure will not be validated, use `makeBAC` instead.
fromEdges :: [Arrow] -> BAC
fromEdges = fmap (\Arrow {dict, target} -> (dict, target)) .> Map.fromList .> Tree

-- | Arrow to a bounded acyclic category, representing a downward functor.
--   It should be validated by `validate`, or use `makeArrow`.
data Arrow = Arrow {dict :: Dict, target :: BAC} deriving (Eq, Ord, Show)

-- | Dictionary of an arrow, representing mapping of objects between nodes.
type Dict = Map Symbol Symbol

-- | Symbol of a node, representing an object of the corresponding category.
type Symbol = Natural

-- | The base symbol, representing an initial object.
base :: Symbol
base = 0

-- | All symbols of a node.  The first one is the base symbol.
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
symbols :: BAC -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> (base :) .> nubSort

-- | Concatenate two dictionaries:
--
--   > (a `cat` b) ! i = a ! (b ! i)
--
--   It may crash if given dictionaries are not composable.
cat :: HasCallStack => Dict -> Dict -> Dict
cat = fmap . (!)

{- |
A node without descendant (a BAC without proper object).

Examples:

>>> printBAC empty
-}
empty :: BAC
empty = fromEdges []

{- |
a node with only one descendant (a BAC with only one proper object).

Examples:

>>> printBAC $ fromJust $ singleton 1
- 0->1

>>> printBAC $ fromJust $ singleton 2
- 0->2
-}
singleton :: Symbol -> Maybe BAC
singleton sym = if sym == base then Nothing else Just $ fromEdges [new_edge]
  where
  new_dict = Map.singleton base sym
  new_node = empty
  new_edge = Arrow {dict = new_dict, target = new_node}

-- | Root arrow of a node.
root :: BAC -> Arrow
root node = Arrow {dict = id_dict, target = node}
  where
  id_dict = node |> symbols |> fmap dupe |> Map.fromList

-- | Join two arrows into one arrow.
--   It may crashes if two arrows are not composable.
join :: HasCallStack => Arrow -> Arrow -> Arrow
join arr1 arr2 = arr2 {dict = dict arr1 `cat` dict arr2}

-- | Divide two arrows.  The first is divisor and the second is the dividend, and they
--   should start at the same node.
--   It obeys the following law:
--
--   > arr23 `elem` divide arr12 arr13  ->  arr12 `join` arr23 == arr13
divide :: Arrow -> Arrow -> [Arrow]
divide arr12 arr13 =
  arr12
  |> dict
  |> Map.toList
  |> filter (snd .> (== symbol arr13))
  |> fmap fst
  |> nubSort
  |> fmap (arrow (target arr12) .> fromJust)

-- | Extend an arrow by joining to the edges of the target node.
extend :: Arrow -> [Arrow]
extend arr = target arr |> edges |> fmap (join arr)

-- | The relative location between nodes.
data Location = Inner | Boundary | Outer deriving (Eq, Ord, Show)

-- | Relative location of the node referenced by the given symbol with respect to a given
--   arrow.
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
locate :: Arrow -> Symbol -> Location
locate arr sym
  | symbol arr == sym   = Boundary
  | sym `elem` dict arr = Inner
  | otherwise           = Outer

-- | Partial order between two arrows.  They should start at the same node.
--   It crashes with inconsistencies caused by bad data.
--
--   Examples:
--
--   >>>  fromJust (arrow cone 4) `compare` fromJust (arrow cone 6)
--   Just LT
--
--   >>>  fromJust (arrow cone 4) `compare` fromJust (arrow cone 4)
--   Just EQ
--
--   >>> fromJust (arrow cone 2) `compare` fromJust (arrow cone 6)
--   Nothing
compare :: HasCallStack => Arrow -> Arrow -> Maybe Ordering
compare arr1 arr2 =
  case (locate arr1 (symbol arr2), locate arr2 (symbol arr1)) of
    (Boundary, Boundary) -> Just EQ
    (Inner, Outer) -> Just LT
    (Outer, Inner) -> Just GT
    (Outer, Outer) -> Nothing
    _ -> error "invalid state"

-- | An arrow to the node referenced by the given symbol, or `Nothing` if it is outside
--   the node.
--
--   Examples:
--
--   >>> arrow cone 3
--   Just (Arrow {dict = fromList [(0,3),(1,4),(2,2),(3,6),(4,4)], target = ...
--
--   >>> arrow cone 5
--   Nothing
arrow :: BAC -> Symbol -> Maybe Arrow
arrow node sym = go (root node)
  where
  go arr = case locate arr sym of
    Outer    -> Nothing
    Boundary -> Just arr
    Inner    -> Just $ arr |> extend |> mapMaybe go |> head

-- | The symbol referencing to the given arrow.
--   It is the inverse of `arrow`:
--
--   Examples:
--
--   >>> fmap symbol (arrow cone 3)
--   Just 3
--
--   >>> fmap symbol (arrow cone 5)
--   Nothing
symbol :: Arrow -> Symbol
symbol = dict .> (! base)

-- | A 2-chain referenced by the given pair of symbols.
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
arrow2 :: BAC -> (Symbol, Symbol) -> Maybe (Arrow, Arrow)
arrow2 node (src, tgt) = do
  src_arr <- arrow node src
  tgt_subarr <- arrow (target src_arr) tgt
  return (src_arr, tgt_subarr)

-- | The pair of symbols referencing to the given 2-chain.
--   It is the inverse of `arrow2`:
--
--   Examples:
--
--   >>> fmap symbol2 (arrow2 cone (3,2))
--   Just (3,2)
--
--   >>> fmap symbol2 (arrow2 cone (1,2))
--   Nothing
symbol2 :: (Arrow, Arrow) -> (Symbol, Symbol)
symbol2 = symbol `bimap` symbol

-- | Find prefix edges of paths from a node to a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` prefix node sym
--   > ->  arr1 `elem` edges node
--   > &&  symbol (arr1 `join` arr2) == sym
prefix :: BAC -> Symbol -> [(Arrow, Arrow)]
prefix node sym =
  arrow node sym
  |> maybe [] \tgt_arr ->
    node
    |> edges
    |> concatMap \arr ->
      divide arr tgt_arr
      |> fmap (arr,)

-- | Find suffix edges of paths from a node to a given symbol.
--   It obeys the following law:
--
--   > (arr1, arr2) `elem` suffix node sym
--   > ->  arr2 `elem` edges (target arr1)
--   > &&  symbol (arr1 `join` arr2) == sym
suffix :: BAC -> Symbol -> [(Arrow, Arrow)]
suffix node sym =
  arrowsUnder node sym
  |> sortOn symbol
  |> concatMap \curr ->
    curr
    |> target
    |> edges
    |> filter (join curr .> symbol .> (== sym))
    |> fmap (curr,)

-- | Find all suffix arrows of paths from a node to a given symbol.
allSuffix :: BAC -> Symbol -> [(Arrow, Arrow)]
allSuffix node sym =
  arrowsUnder node sym
  |> concatMap \curr ->
    curr `divide` tgt_arr |> fmap (curr,)
  where
  tgt_arr = arrow node sym |> fromJust

-- | Extend a tuple of arrows.
--   It obeys the following law:
--
--   > (arr13, arr34) `elem` extend2 (arr12, arr24)
--   > ->  arr13 `elem` extend arr12
--   > &&  arr12 `join` arr24 == arr13 `join` arr34
extend2 :: (Arrow, Arrow) -> [(Arrow, Arrow)]
extend2 (arr1, arr2) =
  target arr1
  |> edges
  |> filter ((`locate` symbol arr2) .> (/= Outer))
  |> concatMap \arr ->
    arr `divide` arr2
    |> fmap (arr1 `join` arr,)

-- | Divide two tuples of arrows.  The first is divisor and the second is the dividend,
--   and they should start and end at the same node.
--   It obeys the following laws:
--
--   > arr12 `join` arr24  ==  arr13 `join` arr34
--
--   > arr23 `elem` divide2 (arr12, arr24) (arr13, arr34)
--   > ->  arr12 `join` arr23 == arr13
--   > &&  arr23 `join` arr34 == arr34
divide2 :: (Arrow, Arrow) -> (Arrow, Arrow) -> [Arrow]
divide2 (arr12, arr24) (arr13, arr34) =
  arr12 `divide` arr13 |> filter \arr23 ->
    symbol (arr23 `join` arr34) == symbol arr24


-- | Check if the given symbol reference to a nondecomposable initial morphism.
--
--   Examples:
--
--   >>> nondecomposable cone 3
--   True
--
--   >>> nondecomposable cone 4
--   False
--
--   >>> nondecomposable cone 0
--   True
--
--   >>> nondecomposable cone 10
--   False
nondecomposable :: BAC -> Symbol -> Bool
nondecomposable node sym =
  (root node `locate` sym |> (/= Outer))
  && (node |> edges |> all ((`locate` sym) .> (/= Inner)))

-- | Nondecomposable edges of a node.
edgesND :: BAC -> [Arrow]
edgesND node =
  node
  |> edges
  |> filter (symbol .> nondecomposable node)

prefixND :: BAC -> Symbol -> [(Arrow, Arrow)]
prefixND node sym =
  prefix node sym
  |> filter (\(arr1, _) -> nondecomposable node (symbol arr1))

suffixND :: BAC -> Symbol -> [(Arrow, Arrow)]
suffixND node sym =
  suffix node sym
  |> filter (\(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))


-- | Check if an arrow is valid.  To validate a node, try @validate (root node)@.
--   See [Types]("BAC.Base#g:types") for detail.
validate :: Arrow -> Bool
validate arr = validateDicts && validateSup
  where
  validateDicts = Map.keys (dict arr) == symbols (target arr)
  validateSup =
    extend arr
    |> fmap dupe
    |> fmap (second (target .> arrows))
    |> concatMap sequence
    |> fmap (uncurry join)
    |> (arr :)
    |> groupSortOn symbol
    |> all allSame

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
validateAll :: Arrow -> Bool
validateAll arr = validateChildren && validate arr
  where
  validateChildren = target arr |> edges |> all validateAll

-- | Make a node with validation.
makeBAC :: [Arrow] -> Maybe BAC
makeBAC = fromEdges .> guarded (root .> validate)

-- | Make an arrow with validation.
makeArrow :: Dict -> BAC -> Maybe Arrow
makeArrow dict target = Arrow {dict = dict, target = target} |> guarded validate


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
--   >>> fold (\curr results -> concat results `snoc` symbol curr) cone
--   [2,1,2,6,4,2,6,4,3,0]
--
--   >>> fold (\curr results -> concat results `snoc` symbol curr) crescent
--   [3,2,3,4,3,2,3,4,1,0]
--
--   >>> fold (\curr results -> concat results `snoc` symbol curr) torus
--   [3,3,2,3,3,5,3,3,2,3,3,5,1,0]
--
--   >>> import Debug.Trace (traceShow)
--   >>> fold (\curr results -> results == results `seq` traceShow (symbol curr) ()) torus `seq` return ()
--   3
--   2
--   5
--   1
--   0
fold ::
  (Arrow -> [r] -> r)  -- ^ The function to reduce a node and the results from its child
                       --   nodes into a value.
  -> BAC              -- ^ The root node of BAC to fold.
  -> r                 -- ^ The folding result.
fold f = root .> memoizeWithKey symbol \self curr -> do
  res <- curr |> extend |> traverse self
  return $ f curr res

-- | Fold a BAC under a node.
--
--   Examples:
--
--   >>> foldUnder 6 (\_ results -> "<" ++ concat (mapMaybe fromInner results) ++ ">") cone
--   AtInner "<<<><>>>"
--
--   >>> foldUnder 6 (\curr results -> concat (mapMaybe fromInner results) `snoc` symbol curr) cone
--   AtInner [4,4,3,0]
--
--   >>> import Debug.Trace (traceShow)
--   >>> res = foldUnder 6 (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
--   >>> res == res `seq` return ()
--   4
--   3
--   0
foldUnder ::
  Symbol                          -- ^ The symbol referencing to the boundary.
  -> (Arrow -> [Located r] -> r)  -- ^ The reduce function.  Where the results of child
                                  --   nodes are labeled by `Located`.
  -> BAC                         -- ^ The root node of BAC to fold.
  -> Located r                    -- ^ The folding result, which is labeled by `Located`.
foldUnder sym f = root .> memoizeWithKey symbol \self curr ->
  case locate curr sym of
    Outer    -> return AtOuter
    Boundary -> return AtBoundary
    Inner    -> do
      res <- curr |> extend |> traverse self
      return $ AtInner (f curr res)

-- | Modify edges of BAC.
modify ::
  ((Arrow, Arrow) -> BAC -> [Arrow])
              -- ^ The function to modify edge.  The first parameter is the original edge
              --   to modified, and the second parameter is the modified target node.  It
              --   should return a list of modified edges.
  -> BAC   -- ^ The root node of BAC to modify.
  -> BAC   -- ^ The modified result.
modify f =
  fold \curr results -> fromEdges do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | Modify edges of BAC under a node.
modifyUnder ::
  Symbol                -- ^ The symbol referencing to the boundary.
  -> ((Arrow, Arrow) -> Located BAC -> [Arrow])
                        -- ^ The modify function.  Where the results of child nodes are
                        --   labeled by `Located`.
  -> BAC               -- ^ The root node of BAC to modify.
  -> Located BAC       -- ^ The modified result, which is labeled by `Located`.
modifyUnder sym f =
  foldUnder sym \curr results -> fromEdges do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | All arrows of this node in evalution order of fold.
--   It is equivalent to @fold (\curr results -> concat results `snoc` curr) .> nubOn symbol@.
--
--   Examples:
--
--   >>> fmap symbol $ arrows cone
--   [2,1,6,4,3,0]
--
--   >>> fmap symbol $ arrows crescent
--   [3,2,4,1,0]
--
--   >>> fmap symbol $ arrows torus
--   [3,2,5,1,0]
arrows :: BAC -> [Arrow]
arrows = root .> go [] .> fmap snd
  where
  go res curr
    | sym `elem` fmap fst res = res
    | otherwise               = curr |> extend |> foldl' go res |> (`snoc` (sym, curr))
    where
    sym = symbol curr

-- | All arrows under a given symbol of this node in evalution order of foldUnder.
--
--   Examples:
--
--   >>> fmap symbol $ arrowsUnder cone 6
--   [4,3,0]
--
--   >>> fmap symbol $ arrowsUnder cone 5
--   []
arrowsUnder :: BAC -> Symbol -> [Arrow]
arrowsUnder node sym = node |> root |> go [] |> fmap snd
  where
  go res curr
    | locate curr sym /= Inner = res
    | sym' `elem` fmap fst res = res
    | otherwise                = curr |> extend |> foldl' go res |> (`snoc` (sym', curr))
    where
    sym' = symbol curr

-- | Fold a BAC reversely.
--
--   Examples:
--
--   >>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) cone
--   [(6,[0,3,0,3,4,6]),(2,[0,1,0,3,0,3,4,2])]
--
--   >>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) crescent
--   [(3,[0,1,0,1,2,0,1,0,1,4,3])]
--
--   >>> fmap (first symbol) $ cofold (\curr results -> concatMap snd results `snoc` symbol curr) torus
--   [(3,[0,1,0,1,2,0,1,0,1,2,0,1,0,1,5,0,1,0,1,5,3])]
--
--   >>> import Debug.Trace (traceShow)
--   >>> res = cofold (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
--   >>> res == res `seq` return ()
--   0
--   3
--   4
--   6
--   1
--   2
cofold :: (Arrow -> [((Arrow, Arrow), r)] -> r) -> BAC -> [(Arrow, r)]
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
      |> fmap (\arr -> (curr `join` arr, ((curr, arr), value)))
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


-- | Fold a BAC reversely under a node.
--
--   Examples:
--
--   >>> cofoldUnder 6 (\curr results -> concatMap snd results `snoc` symbol curr) cone
--   Just [0,3,0,3,4,6]
--
--   >>> import Debug.Trace (traceShow)
--   >>> res = cofoldUnder 6 (\curr results -> results == results `seq` traceShow (symbol curr) ()) cone
--   >>> res == res `seq` return ()
--   0
--   3
--   4
--   6
cofoldUnder :: Symbol -> (Arrow -> [((Arrow, Arrow), r)] -> r) -> BAC -> Maybe r
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
      |> fmap (\arr -> (curr `join` arr, ((curr, arr), value)))
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
