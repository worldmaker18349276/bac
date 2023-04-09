{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
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
  Node,
  edges,
  fromEdges,
  Arrow (..),
  Dict,
  Symbol,
  base,
  symbols,
  cat,

  -- -- ** Arrow #arrow#

  root,
  join,
  divide,
  extend,
  Location (..),
  locate,
  arrow,
  symbol,

  -- ** Tuple of Arrows

  arrow2,
  symbol2,
  prefix,
  suffix,
  extend2,
  divide2,

  -- ** Nondecomposable

  nondecomposable,
  edgesND,
  prefixND,
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
  forwardSymbolTrieUnder,
  backwardSymbolTrieUnder,
  lowerIso,

  -- * Folding #folding#

  Located (..),
  fromReachable,
  fromInner,
  fold,
  foldUnder,
  modify,
  modifyUnder,
  arrows,
  arrowsUnder,
  cofold,
  cofoldUnder,

  -- * Non-Categorical Operations #operations#

  rewireEdges,
  relabelObject,
) where

import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Foldable (Foldable (foldl'))
import Data.List (elemIndex, sort, sortOn, transpose, intercalate)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, snoc)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (dupe)
import GHC.Stack (HasCallStack)
import Numeric.Natural (Natural)
import Prelude hiding (map)

import Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet)
import Utils.Memoize (memoizeWithKey)
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Map (fromList, elems)

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

-- | The node of the tree representation of a bounded acyclic category.
--   It should be validated by @validate . root@.
type Node = Tree Dict

-- | The arrows of edges of the given node.
edges :: Node -> [Arrow]
edges (Tree m) = m |> Map.toList |> fmap (uncurry Arrow)

-- | Construct a node by edges.  The structure will not be validated, use `makeNode` instead.
fromEdges :: [Arrow] -> Node
fromEdges = fmap (\Arrow {dict, target} -> (dict, target)) .> Map.fromList .> Tree

-- | Arrow of a bounded acyclic category, representing a downward functor.
--   It should be validated by `validate`, or use `makeArrow`.
data Arrow = Arrow {dict :: Dict, target :: Node} deriving (Eq, Ord, Show)

-- | Dictionary of an arrow, representing mapping between objects.
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
symbols :: Node -> [Symbol]
symbols = edges .> concatMap (dict .> Map.elems) .> (base :) .> nubSort

-- | Concatenate two dictionaries:
--
--   > (a `cat` b) ! i = a ! (b ! i)
--
--   It may crash if given dictionaries are not composable.
cat :: HasCallStack => Dict -> Dict -> Dict
cat = fmap . (!)

-- | Root arrow of a node.
root :: Node -> Arrow
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
arrow :: Node -> Symbol -> Maybe Arrow
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
arrow2 :: Node -> (Symbol, Symbol) -> Maybe (Arrow, Arrow)
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
prefix :: Node -> Symbol -> [(Arrow, Arrow)]
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
suffix :: Node -> Symbol -> [(Arrow, Arrow)]
suffix node sym =
  node
  |> arrowsUnder sym
  |> sortOn symbol
  |> concatMap \curr ->
    curr
    |> target
    |> edges
    |> filter (join curr .> symbol .> (== sym))
    |> fmap (curr,)

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
nondecomposable :: Node -> Symbol -> Bool
nondecomposable node sym =
  (root node `locate` sym |> (/= Outer))
  && (node |> edges |> all ((`locate` sym) .> (/= Inner)))

-- | Nondecomposable edges of a node.
edgesND :: Node -> [Arrow]
edgesND node =
  node
  |> edges
  |> filter (symbol .> nondecomposable node)

prefixND :: Node -> Symbol -> [(Arrow, Arrow)]
prefixND node sym =
  prefix node sym
  |> filter (\(arr1, _) -> nondecomposable node (symbol arr1))

suffixND :: Node -> Symbol -> [(Arrow, Arrow)]
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
makeNode :: [Arrow] -> Maybe Node
makeNode = fromEdges .> guarded (root .> validate)

-- | Make an arrow with validation.
makeArrow :: Dict -> Node -> Maybe Arrow
makeArrow dict target = Arrow {dict = dict, target = target} |> guarded validate

-- | Structural equality, the equality of nodes up to rewiring.
--   The symbols of nodes should be the same, and equality of child nodes are not checked.
--   The node with the same structure can be unioned by merging their edges.
eqStruct :: [Node] -> Bool
eqStruct = fmap edgesND .> fmap (fmap dict) .> allSame

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
canonicalize :: Node -> [Dict]
canonicalize =
  edgesND
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
canonicalizeObject :: Node -> Symbol -> Maybe [Dict]
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
    |> edgesND
    |> fmap dict
    |> fmap Map.elems
    |> canonicalizeGradedEqlistSet (keys !)
    |> fmap (base :)
    |> fmap ((`zip` [base..]) .> Map.fromList)

-- | Collect all maximum chains to a node into a trie.
--   It is a tree such that its paths correspond to maximum chains, which is represented
--   as a sequence of symbols, and each symbol indicates a nondecomposable morphism.  Just
--   like BAC, the nodes of this trie is implicitly shared.
--
--   Examples:
--
--   >>> putStr $ showTree $ fromJust $ forwardSymbolTrieUnder 6 cone
--   {3:{1:{2:{}},4:{2:{}}}}
forwardSymbolTrieUnder :: Symbol -> Node -> Maybe (Tree Symbol)
forwardSymbolTrieUnder sym = fromReachable res0 . foldUnder sym \curr results ->
  edges (target curr) `zip` results
  |> mapMaybe (second (fromReachable res0) .> sequence)
  |> fmap (first symbol)
  |> filter (fst .> nondecomposable (target curr))
  |> Map.fromList
  |> Tree
  where
  res0 = Tree Map.empty

-- | Collect all maximum chains to a node into a reversed trie.
--   It is a tree such that its paths correspond to the reverse of maximum chains, which
--   is represented as a sequence of pairs of symbols, and each pair of symbols indicates
--   a nondecomposable morphism.  Just like BAC, the nodes of this trie is implicitly
--   shared.
--
--   Examples:
--
--   >>> putStr $ showTree $ fromJust $ backwardSymbolTrieUnder 6 cone
--   {(4,2):{(3,1):{(0,3):{}},(3,4):{(0,3):{}}}}
backwardSymbolTrieUnder :: Symbol -> Node -> Maybe (Tree (Symbol, Symbol))
backwardSymbolTrieUnder sym = cofoldUnder sym \_curr results ->
  results
  |> filter (fst .> \(arr1, arr2) -> nondecomposable (target arr1) (symbol arr2))
  |> fmap (first symbol2)
  |> Map.fromList
  |> Tree

{- |
Check lower isomorphisms for given symbols.

Examples:

>>> lowerIso [2,4] [[0,1::Int], [0,1]] crescent
True
-}
lowerIso ::
  Eq k
  => [Symbol]  -- ^ The symbols to check.
  -> [[k]]     -- ^ The keys to classify nondecomposable incoming morphisms.
  -> Node
  -> Bool
lowerIso [] _ _ = True
lowerIso [_] _ _ = True
lowerIso tgts keys node = isJust do
  let tgt_pars = tgts |> fmap (suffixND node)
  guard $ tgt_pars |> fmap length |> allSame
  guard $ length keys == length tgt_pars
  guard $ keys `zip` tgt_pars |> fmap (length `bimap` length) |> all (uncurry (==))

  guard $ keys |> all (anySame .> not)
  indices <- keys |> traverse (traverse (`elemIndex` head keys))
  let merging_symbols =
        zip tgt_pars indices
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose
        |> fmap (fmap symbol2)
  guard $ merging_symbols |> all (fmap fst .> allSame)

  sequence_ $ node |> foldUnder (head tgts) \curr results -> do
    results' <- results |> traverse sequence

    let collapse = nubSort $ fmap sort do
          (lres, edge) <- results' `zip` edges (target curr)
          case lres of
            AtOuter -> mzero
            AtInner res -> res |> fmap (fmap (dict edge !))
            AtBoundary ->
              merging_symbols
              |> filter (head .> fst .> (== symbol curr))
              |> fmap (fmap snd)

    guard $ collapse |> concat |> anySame |> not

    return collapse

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
  -> Node              -- ^ The root node of BAC to fold.
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
  -> Node                         -- ^ The root node of BAC to fold.
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
  ((Arrow, Arrow) -> Node -> [Arrow])
              -- ^ The function to modify edge.  The first parameter is the original edge
              --   to modified, and the second parameter is the modified target node.  It
              --   should return a list of modified edges.
  -> Node   -- ^ The root node of BAC to modify.
  -> Node   -- ^ The modified result.
modify f =
  fold \curr results -> fromEdges do
    (res, edge) <- results `zip` edges (target curr)
    f (curr, edge) res

-- | Modify edges of BAC under a node.
modifyUnder ::
  Symbol                -- ^ The symbol referencing to the boundary.
  -> ((Arrow, Arrow) -> Located Node -> [Arrow])
                        -- ^ The modify function.  Where the results of child nodes are
                        --   labeled by `Located`.
  -> Node               -- ^ The root node of BAC to modify.
  -> Located Node       -- ^ The modified result, which is labeled by `Located`.
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
arrows :: Node -> [Arrow]
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
--   >>> fmap symbol $ arrowsUnder 6 cone
--   [4,3,0]
--
--   >>> fmap symbol $ arrowsUnder 5 cone
--   []
arrowsUnder :: Symbol -> Node -> [Arrow]
arrowsUnder sym = root .> go [] .> fmap snd
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
cofold :: (Arrow -> [((Arrow, Arrow), r)] -> r) -> Node -> [(Arrow, r)]
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
cofoldUnder :: Symbol -> (Arrow -> [((Arrow, Arrow), r)] -> r) -> Node -> Maybe r
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

{- |
Rewire edges of a given node.

Examples:

>>> printNode $ fromJust $ rewireEdges 0 [1, 4, 3] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1
- 0->4; 1->2; 2->6
  *1

>>> printNode $ fromJust $ rewireEdges 3 [1, 4, 3] cone
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
  - 0->3
    *2
  - 0->4; 1->2; 2->3
    *1

>>> rewireEdges 3 [1, 5, 3] cone
Nothing
-}
rewireEdges ::
  Symbol         -- ^ The symbol referencing to the node to rewire.
  -> [Symbol]    -- ^ The list of values and symbols of rewired edges.
  -> Node        -- ^ The root node of BAC.
  -> Maybe Node  -- ^ The result.
rewireEdges src tgts node = do
  src_arr <- arrow node src
  let nd_syms = target src_arr |> edgesND |> fmap symbol
  src_edges' <- tgts |> traverse (arrow (target src_arr))
  let res0 = fromEdges src_edges'

  let nd_syms' = res0 |> edgesND |> fmap symbol
  guard $ nd_syms == nd_syms'

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {target = res0}

{- |
Relabel a given node.

Examples:

>>> let remap = fromList [(0,0), (1,4), (2,1), (3,2), (4,3)] :: Dict
>>> printNode $ fromJust $ relabelObject 3 remap cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2; 2->6; 3->4; 4->4
  - 0->3; 1->1; 2->2
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->1; 2->2
    *1

>>> relabelObject 3 (fromList [(0,0), (1,4), (2,1), (3,2)]) cone
Nothing

>>> relabelObject 3 (fromList [(0,0), (1,4), (2,1), (3,2), (4,4)]) cone
Nothing

>>> relabelObject 3 (fromList [(0,3), (1,4), (2,1), (3,2), (4,0)]) cone
Nothing
-}
relabelObject ::
  Symbol         -- ^ The symbol referencing to the node to relabel.
  -> Dict        -- ^ The dictionary to relabel the symbols of the node.
  -> Node        -- ^ The root node of BAC.
  -> Maybe Node  -- ^ The result.
relabelObject tgt mapping node = do
  tgt_arr <- arrow node tgt
  guard $ base `Map.member` mapping && mapping ! base == base
  guard $ Map.keys mapping == symbols (target tgt_arr)
  let unmapping = mapping |> Map.toList |> fmap swap |> Map.fromList
  guard $ length unmapping == length mapping

  let res0 = fromEdges do
        edge <- edges (target tgt_arr)
        return edge {dict = mapping `cat` dict edge}
  fromReachable res0 $ node |> modifyUnder tgt \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict edge `cat` unmapping, target = res0}
