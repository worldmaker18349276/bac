{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental (
  Mutation (..),

  -- * Restructure #restructure#

  rewire,
  addEdge,
  removeEdge,
  relabel,
  relabelRoot,
  alterSymbol,

  addEdgeMutation,
  removeEdgeMutation,
  relabelMutation,
  relabelRootMutation,
  alterSymbolMutation,

  -- * Empty, Singleton

  empty,
  singleton,

  -- * Remove Symbol, Node

  missingAltPathsOfArrow,
  missingAltPathsOfNode,
  removeNDSymbol,
  removeNode,
  removeRootNDSymbol,
  removeRootNDSymbol',
  removeLeafNode,
  removeLeafNode',

  removeNDSymbolMutation,
  removeNodeMutation,
  removeRootNDSymbolMutation,
  removeLeafNodeMutation,

  -- * Add Symbol, Node

  Coangle,
  Angle,
  validateCoangle,
  validateAngle,
  compatibleAngles,
  compatibleCoangles,
  compatibleCoanglesAngles,
  findValidCoanglesAngles,
  addNDSymbol,
  appendNode,
  insertNode,

  addNDSymbolMutation,

  -- * Duplicate Symbol, Node

  duplicateNDSymbol,
  duplicateNDSymbol',
  duplicateNode,
  duplicateNode',
  duplicateRootNDSymbol,
  duplicateLeafNode,

  duplicateNDSymbolMutation,
  duplicateNodeMutation,
  duplicateRootNDSymbolMutation,
  duplicateLeafNodeMutation,

  -- * Split Symbol, Node

  partitionPrefix,
  partitionSymbols,
  makeSplitter,
  splitSymbol,
  splitRootSymbol,
  splitNode,
  splitRootNode,

  splitSymbolMutation,
  splitRootSymbolMutation,
  splitNodeMutation,

  -- * Merge Symbols, Nodes

  mergeSymbols,
  mergeRootSymbols,
  mergeNodes,
  mergeRootNodes,
  expandMergingSymbols,
  mergeSymbolsAggressively,

  mergeSymbolsMutation,
  mergeRootSymbolsMutation,
) where

import Control.Arrow ((&&&))
import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first, second, bimap))
import Data.Foldable (find)
import Data.Foldable.Extra (notNull)
import Data.List (elemIndex, elemIndices, findIndex, nub, sort, sortOn, transpose)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, (!?), snoc, groupOnKey)
import Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isJust, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both, dupe)
import Numeric.Natural (Natural)

import BAC.Base
import BAC.Isomorphism
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils (foldlMUncurry, guarded, (.>), (|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Map (fromList)

-- | A mark indicating mutations of symbols.  `Permutation` indicates exchanging symbols;
--   `Duplication` indicates duplicating a symbol; `Contraction` indicates merging symbols;
--   `Deletion` indicates removing a symbol; `Insertion` indicates adding a symbol.
data Mutation =
    Permutation [(Symbol, Symbol)] [(Symbol, Symbol)]
  | Duplication  (Symbol, Symbol)  [(Symbol, Symbol)]
  | Contraction [(Symbol, Symbol)]  (Symbol, Symbol)
  | Deletion     (Symbol, Symbol)
  | Insertion                       (Symbol, Symbol)

{- |
Rewire edges of a given node.

Examples:

>>> printBAC $ fromJust $ rewire 0 [1, 4, 3] cone
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

>>> printBAC $ fromJust $ rewire 3 [1, 4, 3] cone
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

>>> rewire 3 [1, 5, 3] cone
Nothing
-}
rewire ::
  Symbol         -- ^ The symbol referencing to the node to rewire.
  -> [Symbol]    -- ^ The list of pairs of symbols of rewired edges.
  -> BAC
  -> Maybe BAC
rewire src tgts node = do
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

{- | Add an edge.  The categorical structure should not change after adding this edge.

Examples:

>>> printBAC $ fromJust $ cone |> addEdge (3,2)
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->2
    *0
  - 0->4; 1->2; 2->3
    *1
-}
addEdge ::
  (Symbol, Symbol)  -- ^ The pair of symbols of added edge.
  -> BAC
  -> Maybe BAC
addEdge (src, tgt) node = do
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let new_syms =
        src_arr
        |> target
        |> edges
        |> fmap symbol
        |> (`snoc` tgt)
  node |> rewire src new_syms

addEdgeMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
addEdgeMutation (src, tgt) _node = [Insertion (src, tgt)]

{- | Remove an edge.  The categorical structure should not change after removing this edge.

Examples:

>>> cone' = fromJust $ cone |> addEdge (3,2)
>>> printBAC $ fromJust $ cone' |> removeEdge (3,2)
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
-}
removeEdge ::
  (Symbol, Symbol)  -- ^ The pair of symbols of removed edge.
  -> BAC
  -> Maybe BAC
removeEdge (src, tgt) node = do
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let new_syms =
        src_arr
        |> target
        |> edges
        |> fmap symbol
        |> filter (/= tgt)
  node |> rewire src new_syms

removeEdgeMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
removeEdgeMutation (src, tgt) _node = [Deletion (src, tgt)]

{- |
Relabel symbols in a given node.

Examples:

>>> let remap = fromList [(0,0), (1,4), (2,1), (3,2), (4,3)] :: Dict
>>> printBAC $ fromJust $ relabel 3 remap cone
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

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2)]) cone
Nothing

>>> relabel 3 (fromList [(0,0), (1,4), (2,1), (3,2), (4,4)]) cone
Nothing

>>> relabel 3 (fromList [(0,3), (1,4), (2,1), (3,2), (4,0)]) cone
Nothing
-}
relabel ::
  Symbol    -- ^ The symbol referencing to the node to relabel.
  -> Dict   -- ^ The dictionary to relabel the symbols of the node.
  -> BAC
  -> Maybe BAC
relabel tgt mapping node = do
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

relabelMutation :: Symbol -> Dict -> BAC -> [Mutation]
relabelMutation tgt mapping node =
  arrow node tgt
  |> fromJust
  |> target
  |> edges
  |> fmap symbol
  |> fmap (id &&& (mapping !))
  |> fmap (both (tgt,))
  |> unzip
  |> uncurry Permutation
  |> (: [])
  |> if tgt == base then (++ root_mutation) else id
  where
  root_mutation =
    mapping
    |> Map.toList
    |> concatMap \(sym, sym') ->
      arrow node sym
      |> fromJust
      |> target
      |> edges
      |> fmap symbol
      |> fmap dupe
      |> fmap ((sym,) `bimap` (sym',))
      |> unzip
      |> uncurry Permutation
      |> (: [])

-- | Relabel symbols in the root node.
relabelRoot :: Dict -> BAC -> Maybe BAC
relabelRoot = relabel base

relabelRootMutation :: Dict -> BAC -> [Mutation]
relabelRootMutation = relabelMutation base

{- |
Alter a symbol in a node.

Examples:

>>> printBAC $ fromJust $ alterSymbol (3, 1) 5 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6; 4->4; 5->4
  - 0->4; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->5; 1->2; 2->3
    *1
-}
alterSymbol ::
  (Symbol, Symbol)  -- ^ The pair of symbols to be altered.
  -> Symbol         -- ^ The new symbol.
  -> BAC
  -> Maybe BAC
alterSymbol (src, tgt) sym node = do
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let syms = src_arr |> target |> symbols
  guard $ syms |> filter (/= tgt) |> notElem sym
  let mapping = syms |> fmap dupe |> Map.fromList |> Map.insert tgt sym
  node |> relabel src mapping

alterSymbolMutation :: (Symbol, Symbol) -> Symbol -> BAC -> [Mutation]
alterSymbolMutation (src, tgt) sym node =
  arrow node src
  |> fromJust
  |> target
  |> edges
  |> fmap symbol
  |> elem tgt
  |> (\case
    False -> []
    True -> [Permutation [(src, tgt)] [(src, sym)]]
  )
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap dupe
    |> fmap ((tgt,) `bimap` (sym,))
    |> unzip
    |> uncurry Permutation
    |> (: [])

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

{- |
Find all missing alternative paths for a nondecomposable morphism, which are necessary for
removing this morphism.

Examples:

>>> missingAltPathsOfArrow (3,1) cone
Just ([],[])

>>> missingAltPathsOfArrow (4,2) cone
Just ([(3,3)],[])

>>> missingAltPathsOfArrow (0,3) cone
Just ([],[(0,4)])
-}
missingAltPathsOfArrow ::
  (Symbol, Symbol)  -- ^ The tuple of symbols indicating the morphism to be removed.
  -> BAC            -- ^ The root node of BAC.
  -> Maybe ([(Symbol, Symbol)], [(Symbol, Symbol)])
                    -- ^ Tuples of symbols indicating the edges need to be added.
                    --   The first list is the edges skipping the source object, and the
                    --   second list is the edges skipping the target object.
missingAltPathsOfArrow (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, tgt_arr) <- arrow2 node (src, tgt)
  guard $ nondecomposable (target src_arr) tgt
  let src_alts = nubSort do
        (arr1, arr2) <- src |> suffixND node
        guard $
          suffix (target arr1) (symbol (arr2 `join` tgt_arr))
          |> all (first (join arr1) .> symbol2 .> (== (src, tgt)))
        return $ symbol2 (arr1, arr2 `join` tgt_arr)
  let tgt_alts = nubSort do
        arr <- target tgt_arr |> edgesND
        guard $
          prefix (target src_arr) (symbol (tgt_arr `join` arr))
          |> all (fst .> (src_arr,) .> symbol2 .> (== (src, tgt)))
        return $ symbol2 (src_arr, tgt_arr `join` arr)
  return (src_alts, tgt_alts)

missingAltPathsOfNode ::
  Symbol            -- ^ The symbol indicating the object to be removed.
  -> BAC            -- ^ The root node of BAC.
  -> Maybe [(Symbol, Symbol)]
                    -- ^ Tuples of symbols indicating the edges need to be added.
missingAltPathsOfNode src node = arrow node src |> fmap \src_arr -> do
  let outedges = target src_arr |> edgesND
  (arr1, arr2) <- src |> suffixND node
  arr3 <- outedges
  guard $
    suffix (target arr1) (symbol (arr2 `join` arr3))
    |> all (first (join arr1) .> symbol2 .> (== (src, symbol arr3)))
  return $ symbol2 (arr1, arr2 `join` arr3)

{- |
Remove a nondecomposable symbol in a node (remove a non-terminal nondecomposable morphism).

Examples:

>>> printBAC $ fromJust $ removeNDSymbol (1, 1) cone
- 0->1
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> removeNDSymbol (4, 2) cone
Nothing

>>> cone' = fromJust $ addEdge (0,4) cone
>>> printBAC $ fromJust $ removeNDSymbol (0,3) cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2

>>> :{
printBAC $ fromJust $
  cone
  |> removeNDSymbol (3,1)
  >>= addEdge (3,2)
  >>= addEdge (3,3)
  >>= addEdge (0,4)
  >>= removeNDSymbol (3,4)
:}
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 2->2; 3->6
  - 0->2
    *0
  - 0->3
    &1
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
    *1
-}
removeNDSymbol ::
  (Symbol, Symbol)  -- ^ The tuple of symbols indicating the morphism to be removed.
  -> BAC
  -> Maybe BAC
removeNDSymbol (src, tgt) node = do
  guard $ missingAltPathsOfArrow (src, tgt) node == Just ([],[])

  let src_node = arrow node src |> fromJust |> target
  let res0 = src_node |> edges |> filter (\edge -> symbol edge /= tgt) |> fromEdges
  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = filtered_dict, target = res0}
      where
      filtered_dict = dict edge |> Map.delete tgt

removeNDSymbolMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
removeNDSymbolMutation (src, tgt) node =
  [Duplication (src, tgt) []]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap (tgt,)
    |> fmap Deletion

-- | Remove a nondecomposable symbol in the root node (remove a nondecomposable initial
--   morphism).
removeRootNDSymbol :: Symbol -> BAC -> Maybe BAC
removeRootNDSymbol tgt = removeNDSymbol (base, tgt)

removeRootNDSymbolMutation :: Symbol -> BAC -> [Mutation]
removeRootNDSymbolMutation tgt = removeNDSymbolMutation (base, tgt)

{- |
Remove a nondecomposable symbol in the root node step by step (remove a nondecomposable
initial morphism step by step: removing all related morphisms, then splitting category).

Examples:

>>> cone' = fromJust $ addEdge (0,4) cone
>>> printBAC $ fromJust $ removeRootNDSymbol' 3 cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2
-}
removeRootNDSymbol' :: Symbol -> BAC -> Maybe BAC
removeRootNDSymbol' tgt node = do
  guard $
    missingAltPathsOfArrow (0, tgt) node
    |> maybe False \(l, r) -> null l && null r

  let remove_list =
        arrow node tgt
        |> fromJust
        |> target
        |> arrows
        |> fmap symbol
        |> filter (/= base)
        |> fmap (tgt,)
        |> reverse

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let ([], add_list') = node |> missingAltPathsOfArrow sym2 |> fromJust
    node <- (node, add_list') |> foldlMUncurry \(node, add_edge) -> do
      return $ node |> addEdge add_edge |> fromJust

    return $ node |> removeNDSymbol sym2 |> fromJust

  let keys = partitionSymbols node |> fmap (elem tgt)
  return $ node |> splitRootNode keys |> fromJust |> (! False)


-- | Remove a leaf node (remove a nondecomposable terminal morphisms).
removeLeafNode :: Symbol -> BAC -> Maybe BAC
removeLeafNode tgt node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null

  removeNode tgt node

removeLeafNodeMutation :: Symbol -> BAC -> [Mutation]
removeLeafNodeMutation = removeNodeMutation

{- |
Remove an leaf node step by step (remove a nondecomposable terminal morphism step by step:
removing all related morphisms, then splitting category).

Examples:

>>> printBAC $ fromJust $ removeLeafNode' 6 cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 4->4
  - 0->1; 1->2
    &1
    - 0->1
      *0
  - 0->4; 1->2
    *1

>>> printBAC $ fromJust $ removeLeafNode' 2 cone
- 0->1
- 0->3; 1->4; 3->6; 4->4
  - 0->1; 2->3
    &0
    - 0->2
  - 0->4; 2->3
    *0

>>> removeLeafNode' 4 cone
Nothing
-}
removeLeafNode' :: Symbol -> BAC -> Maybe BAC
removeLeafNode' tgt node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  guard $ tgt_arr |> target |> edges |> null

  let remove_list =
        node
        |> arrowsUnder tgt
        |> concatMap ((id &&& (`divide` tgt_arr)) .> sequence .> fmap symbol2)
        |> filter (fst .> (/= base))

  node <- (node, remove_list) |> foldlMUncurry \(node, sym2) -> do
    let (add_list, []) = node |> missingAltPathsOfArrow sym2 |> fromJust
    node <- (node, add_list) |> foldlMUncurry \(node, add_edge) -> do
      return $ node |> addEdge add_edge |> fromJust

    return $ node |> removeNDSymbol sym2 |> fromJust

  let keys = partitionSymbols node |> fmap (elem tgt)
  return $ node |> splitRootNode keys |> fromJust |> (! False)

-- | Two tuples of symbols representing two morphisms where coforks of the first morphism
--   are also coforks of the second morphism.  A cofork of a morphism `f` is a pair of
--   distinct morphisms `g`, 'g'' such that @f . g = f . g'@.  This constraint shows the
--   possibility to add an edge between them.
type Coangle = ((Symbol, Symbol), (Symbol, Symbol))

-- | Two tuples of symbols representing two morphisms where forks of the first morphism are
--   also forks of the second morphism.  A fork of a morphism `f` is a pair of distinct
--   morphisms `g`, 'g'' such that @g . f = g' . f@.  This constraint shows the
--   possibility to add an edge between them.
type Angle = ((Symbol, Symbol), (Symbol, Symbol))

-- | Check whether a given value is a valid coangle.
validateCoangle :: BAC -> Coangle -> Bool
validateCoangle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (fst arr_arr1) == symbol (fst arr_arr2)
  guard $
    fst sym_sym1
    |> suffixND node
    |> groupSortOn (second (`join` snd arr_arr1) .> symbol2)
    |> fmap (fmap (second (`join` snd arr_arr2) .> symbol2))
    |> all allSame

-- | Check whether a given value is a valid angle.
validateAngle :: BAC -> Angle -> Bool
validateAngle node (sym_sym1, sym_sym2) = isJust do
  arr_arr1 <- arrow2 node sym_sym1
  arr_arr2 <- arrow2 node sym_sym2
  guard $ symbol (uncurry join arr_arr1) == symbol (uncurry join arr_arr1)
  guard $
    target (snd arr_arr1)
    |> edgesND
    |> groupSortOn (join (snd arr_arr1) .> symbol)
    |> fmap (fmap (join (snd arr_arr2) .> symbol))
    |> all allSame

-- | Check whether a list of angles are compatible.
--   Angle @(f, g)@ and angle @(f', g')@ are compatible if @h . f = h . f'@ implies
--   @h . g = h . g'@ for all `h`.
compatibleAngles :: BAC -> [Angle] -> Bool
compatibleAngles node =
  traverse (\(sym_sym1, sym_sym2) -> do
    arr_arr1 <- arrow2 node sym_sym1
    arr_arr2 <- arrow2 node sym_sym2
    return $ Map.elems (dict (snd arr_arr1)) `zip` Map.elems (dict (snd arr_arr2))
  )
  .> maybe False (concat .> nubSort .> fmap fst .> anySame .> not)

-- | Check whether a list of coangles are compatible.
--   Coangle @(f, g)@ and coangle @(f', g')@ are compatible if @f . h = f' . h@ implies
--   @g . h = g' . h@ for all `h`.
compatibleCoangles :: BAC -> [Coangle] -> Bool
compatibleCoangles _ [] = True
compatibleCoangles node coangs =
  isJust $ sequence_ $ node |> foldUnder sym0 \curr results -> do
    results' <- traverse sequence results
    let pairs = do
          (res, edge) <- results' `zip` edges (target curr)
          case res of
            AtOuter -> mzero
            AtInner res -> res |> fmap (both (dict edge !))
            AtBoundary ->
              coangs
              |> find (fst .> (== symbol2 (curr, edge)))
              |> fmap (both snd)
              |> maybe mzero return
    pairs |> nubSort |> guarded (fmap fst .> anySame .> not)
  where
  sym0 = coangs |> head |> fst |> fst

-- | Check whether coangles and angles are compatible each others.
--   Coangle @(f, g)@ and angle @(g', f')@ are compatible if @f' . f = g' . g@.
compatibleCoanglesAngles :: BAC -> [Coangle] -> [Angle] -> Bool
compatibleCoanglesAngles node coangs angs =
  isJust $
    angs |> traverse \(sym_sym1, sym_sym2) -> do
      arr_arr1 <- arrow2 node sym_sym1
      arr_arr2 <- arrow2 node sym_sym2
      coangs |> traverse \(sym_sym1', sym_sym2') -> do
        arr_arr1' <- arrow2 node sym_sym1'
        arr_arr2' <- arrow2 node sym_sym2'
        guard $ symbol (uncurry join arr_arr1) == symbol (fst arr_arr2')
        guard $ symbol (uncurry join arr_arr2) == symbol (fst arr_arr1')
        guard $
          symbol (snd arr_arr1 `join` snd arr_arr2')
          == symbol (snd arr_arr2 `join` snd arr_arr1')

{- |
Find all valid coangles and angles, which is used for adding a morphism.  The results are
the angles and coangles need to be selected, or Nothing if it is invalid.

Examples:

>>> fromJust $ findValidCoanglesAngles 1 6 cone
([[((0,1),(0,6))]],[])
-}
findValidCoanglesAngles ::
  Symbol      -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol   -- ^ The symbol indicating the target object of the morphism to be added.
  -> BAC      -- ^ The root node of BAC.
  -> Maybe ([[Coangle]], [[Angle]])
              -- ^ The coangles and angles need to be selected, or Nothing if it is invalid.
findValidCoanglesAngles src tgt node = do
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src == Outer
  let src_alts = sort do
        (arr1, arr2) <- src |> suffixND node
        return $ sort do
          arr2' <- arr1 `divide` tgt_arr
          let ang = (symbol2 (arr1, arr2), symbol2 (arr1, arr2'))
          guard $ validateCoangle node ang
          return ang
  let tgt_alts = sort do
        edge <- target tgt_arr |> edgesND
        return $ sort do
          arr' <- src_arr `divide` (tgt_arr `join` edge)
          let ang = (symbol2 (tgt_arr, edge), symbol2 (src_arr, arr'))
          guard $ validateAngle node ang
          return ang
  return (src_alts, tgt_alts)

{- |
Add a nondecomposable symbol in a node (add a non-terminal nondecomposable morphism).

Examples:

>>> printBAC $ fromJust $ addNDSymbol 1 6 2 [0] [] cone
- 0->1; 1->2; 2->6
  - 0->1
    &0
  - 0->2
    &1
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &2
    - 0->1
      *0
    - 0->2
      *1
  - 0->4; 1->2; 2->3
    *2
-}
addNDSymbol ::
  Symbol     -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol  -- ^ The symbol indicating the target object of the morphism to be added.
  -> Symbol  -- ^ The symbol to be added.
  -> [Int]   -- ^ The indices of coangles given by `findValidCoanglesAngles`.
  -> [Int]   -- ^ The indices of angles given by `findValidCoanglesAngles`.
  -> BAC
  -> Maybe BAC
addNDSymbol src tgt sym src_alts tgt_alts node = do
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src |> (== Outer)

  let (src_angs, tgt_angs) = findValidCoanglesAngles src tgt node |> fromJust
  guard $ length src_angs == length src_alts
  guard $ length tgt_angs == length tgt_alts
  src_angs' <- src_angs `zip` src_alts |> traverse (uncurry (!?))
  tgt_angs' <- tgt_angs `zip` tgt_alts |> traverse (uncurry (!?))

  guard $ compatibleAngles node tgt_angs'
  guard $ compatibleCoanglesAngles node src_angs' tgt_angs'
  guard $ compatibleCoangles node src_angs'
  guard $ target src_arr |> symbols |> notElem sym

  let new_dict =
        tgt_angs'
        |> fmap (both (arrow2 node .> fromJust))
        |> concatMap (both (snd .> dict .> Map.elems) .> uncurry zip)
        |> ((base, sym) :)
        |> nubSort
        |> Map.fromList
  let new_edge = Arrow {dict = new_dict, target = target tgt_arr}

  let find_new_wire (arr1, arr23) =
        suffixND (target arr1) (symbol arr23)
        |> head
        |> \(arr2, arr3) ->
          src_angs'
          |> find (fst .> (== symbol2 (arr1 `join` arr2, arr3)))
          |> fromJust
          |> \(_, (_, s)) -> (dict arr2 ! sym, dict arr2 ! s)

  let res0 = target src_arr |> edges |> (++ [new_edge]) |> fromEdges
  fromReachable res0 $ node |> modifyUnder src \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = new_dict, target = res0}
      where
      new_wire = find_new_wire (curr, edge)
      new_dict = dict edge |> uncurry Map.insert new_wire

addNDSymbolMutation :: Symbol -> Symbol -> Symbol -> [Int] -> [Int] -> BAC -> [Mutation]
addNDSymbolMutation src tgt sym _src_alts _tgt_alts node =
  [Insertion (src, sym)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Duplication (tgt, s) [(tgt, s), (sym, s)]

{- |
Partition the prefixes of a morphism.
It returns a partition of `prefix` of the given symbol, where the objects represented by
the elements in each group are unsplittable in the section category of the arrow specified
by `tgt`.

Examples:

>>> partitionPrefix cone 2
[[(1,1)],[(3,2)]]
-}
partitionPrefix :: BAC -> Symbol -> [[(Symbol, Symbol)]]
partitionPrefix node tgt =
  prefix node tgt
  |> concatMap (\(arr1, arr23) -> suffix (target arr1) (symbol arr23) |> fmap (arr1,))
  |> fmap (\(arr1, (arr2, arr3)) -> ((arr1, arr2 `join` arr3), (arr1 `join` arr2, arr3)))
  |> fmap (both symbol2)
  |> bipartiteEqclass
  |> fmap fst
  |> fmap sort
  |> sort

{- |
Split a symbol on a node (split a non-terminal morphism).

Examples:

>>> printBAC $ fromJust $ splitSymbol (0,2) [2,7] cone
- 0->1; 1->2
  - 0->1
- 0->3; 1->4; 2->7; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> printBAC $ fromJust $ splitSymbol (3,2) [5,6] cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 3->6; 4->4; 5->2; 6->2
  - 0->1; 1->5; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->6; 2->3
    *1
-}
splitSymbol ::
  (Symbol, Symbol)  -- ^ The symbols reference to the morphism to split.
  -> [Symbol]       -- ^ The new symbols of splittable groups given by `partitionPrefix`.
  -> BAC
  -> Maybe BAC
splitSymbol (src, tgt) splitted_syms node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let splittable_groups = partitionPrefix (target src_arr) tgt
  guard $ length splittable_groups == length splitted_syms
  guard $ target src_arr |> symbols |> filter (/= tgt) |> any (`elem` splitted_syms) |> not

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let sym0 = symbol edge
        if sym0 == tgt
        then do
          r' <- splitted_syms
          let split (s, r) = if r == tgt then (s, r') else (s, r)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          return edge {dict = splitted_dict}
        else do
          let split (s, r) = if r == tgt then (s, r') else (s, r)
                where
                r' =
                  splittable_groups
                  |> findIndex ((sym0, s) `elem`)
                  |> fromJust
                  |> (splitted_syms !!)
          let splitted_dict = dict edge |> Map.toList |> fmap split |> Map.fromList
          return edge {dict = splitted_dict}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = merged_dict, target = res0}
      where
      merge (s, r)
        | s == tgt  = [(s', r) | s' <- splitted_syms]
        | otherwise = [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

splitSymbolMutation :: (Symbol, Symbol) -> [Symbol] -> BAC -> [Mutation]
splitSymbolMutation (src, tgt) splitted_syms node =
  [Duplication (src, tgt) (fmap (src,) syms)]
  |> if src == base then (++ root_mutation) else id
  where
  syms = nub splitted_syms
  splittable_groups = arrow node src |> fromJust |> target |> (`partitionPrefix` tgt)
  splitted_groups =
    splitted_syms `zip` splittable_groups
    |> groupOnKey fst
    |> fmap (second (concatMap snd))
  root_mutation =
    splitted_groups
    |> fmap \(sym, group) ->
      Permutation group (fmap (first (const sym)) group)

-- | Split a symbol in the root node (split an initial morphism).
splitRootSymbol :: Symbol -> [Symbol] -> BAC -> Maybe BAC
splitRootSymbol tgt = splitSymbol (base, tgt)

splitRootSymbolMutation :: Symbol -> [Symbol] -> BAC -> [Mutation]
splitRootSymbolMutation tgt = splitSymbolMutation (base, tgt)

{- |
Partition symbols of a object.
It returns a partition of `symbols` of the given node, where the objects represented by
the elements in each group are unsplittable in the given bounded acyclic category.

Examples:

>>> partitionSymbols $ cone
[[1,2,3,4,6]]

>>> partitionSymbols $ target $ fromJust $ arrow crescent 1
[[1,2,3],[5,6,7]]
-}
partitionSymbols :: BAC -> [[Symbol]]
partitionSymbols =
  edges
  .> fmap (dict .> Map.elems)
  .> zip [0 :: Int ..]
  .> concatMap sequence
  .> bipartiteEqclass
  .> fmap (snd .> sort)
  .> sort

makeSplitter :: BAC -> [Natural] -> (Symbol, Symbol) -> [Symbol]
makeSplitter node offsets (src, tgt) = do
  let ran = arrow node src |> fromJust |> target |> symbols |> maximum
  offset <- offsets
  return $ ran * offset + tgt

{- |
Split a node (split a terminal morphism).

Examples:

>>> keys = [0::Natural,1]
>>> splitter = makeSplitter crescent keys .> zip keys .> fromList
>>> printBAC $ fromJust $ splitNode 1 keys splitter crescent
- 0->1; 1->2; 2->3; 3->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
- 0->5; 5->2; 6->3; 7->4
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
-}
splitNode ::
  Ord k
  => Symbol  -- ^ The symbol referencing the node to be splitted.
  -> [k]     -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> ((Symbol, Symbol) -> Map k Symbol)
  -> BAC
  -> Maybe BAC
splitNode tgt splittable_keys splitter node = do
  guard $ locate (root node) tgt |> (== Inner)
  let tgt_arr = arrow node tgt |> fromJust
  let splitted_keys = splittable_keys |> nubSort
  let arrs = arrowsUnder tgt node
  guard $
    arrs
    |> concatMap ((id &&& (`divide` tgt_arr)) .> sequence .> fmap symbol2)
    |> all (splitter .> Map.keys .> (== splitted_keys))
  guard $
    arrs
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> fmap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) |> Map.elems else [s1])
      |> anySame
      |> not

  res0 <-
    arrow node tgt
    |> fromJust
    |> target
    |> splitRootNode splittable_keys
    |> fmap Map.elems
  let splitter' = first symbol .> splitter .> Map.elems

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      duplicate (s, r)
        | dict curr ! r == tgt = splitter' (curr `join` edge, s) `zip` splitter' (curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      (res, sym) <- res0 `zip` splitter' (curr, symbol edge)
      let split (s, r)
            | s == base                    = Just (base, sym)
            | locate (root res) s == Inner = Just (s, r)
            | otherwise                    = Nothing
      let splitted_dict =
            dict edge |> Map.toList |> mapMaybe split |> Map.fromList
      return edge {dict = splitted_dict, target = res}

splitNodeMutation ::
  Ord k
  => Symbol
  -> [k]
  -> ((Symbol, Symbol) -> Map k Symbol)
  -> BAC
  -> [Mutation]
splitNodeMutation tgt splittable_keys splitter node =
  incoming_mutation ++ outgoing_mutation
  where
  incoming_mutation =
    suffix node tgt
    |> fmap symbol2
    |> fmap \(s1, s2) ->
      Duplication (s1, s2) (splitter (s1, s2) |> Map.elems |> fmap (s1,))
  splittable_groups =
    splittable_keys `zip` partitionSymbols node
    |> concatMap sequence
    |> fmap swap
    |> Map.fromList
  outgoing_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> id &&& fmap (\s -> splittable_groups ! s |> (splitter (tgt, s) !))
    |> both (fmap (tgt,))
    |> uncurry Permutation
    |> (: [])

{- |
Split a root node (split a BAC).

Examples:

>>> let crescent_1 = target $ fromJust $ arrow crescent 1
>>> traverse_ printBAC $ fromJust $ splitRootNode [False,True] crescent_1
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2
  - 0->1
    *0
- 0->5; 1->6
  - 0->1
    &0
- 0->7; 1->6
  - 0->1
    *0
-}
splitRootNode ::
  Ord k
  => [k]  -- ^ The keys to classify splittable groups of symbols given by `partitionSymbols`.
  -> BAC
  -> Maybe (Map k BAC)
splitRootNode splittable_keys node = do
  let splittable_groups = partitionSymbols node
  guard $ length splittable_groups == length splittable_keys

  let splitted_keys = splittable_keys |> nub
  let splitted_groups =
        splitted_keys
        |> fmap (`elemIndices` splittable_keys)
        |> fmap (concatMap (splittable_groups !!))

  return $ Map.fromList do
    (key, group) <- splitted_keys `zip` splitted_groups
    let splitted_edges = node |> edges |> filter (symbol .> (`elem` group))
    return (key, fromEdges splitted_edges)


-- | Duplicate a nondecomposable symbol in a node (duplicate a non-terminal
--   nondecomposable morphism).
duplicateNDSymbol :: (Symbol, Symbol) -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbol (src, tgt) syms node = do
  guard $ notNull syms
  src_arr <- arrow node src
  let src_node = target src_arr
  guard $ locate (root src_node) tgt == Inner
  guard $ nondecomposable src_node tgt
  guard $
    src_node
    |> symbols
    |> filter (/= tgt)
    |> (syms ++)
    |> anySame
    |> not

  let res0 = fromEdges do
        edge <- edges src_node
        if symbol edge /= tgt
        then return edge
        else do
          sym <- syms
          let dup_dict = dict edge |> Map.insert base sym
          return $ edge {dict = dup_dict}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> do
      let sym' = Map.lookup tgt (dict edge) |> fromJust
      sym <- syms
      let splitted_dict = dict edge |> Map.delete tgt |> Map.insert sym sym'
      return edge {dict = splitted_dict, target = res0}

duplicateNDSymbolMutation :: (Symbol, Symbol) -> [Symbol] -> BAC -> [Mutation]
duplicateNDSymbolMutation (src, tgt) syms node =
  [Duplication (src, tgt) (fmap (src,) syms)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Duplication (tgt, s) (fmap (,s) syms)

-- | Duplicate a nondecomposable symbol in a node step by step (duplicate a non-terminal
--   nondecomposable morphism step by step).
duplicateNDSymbol' :: (Symbol, Symbol) -> [Symbol] -> BAC -> Maybe BAC
duplicateNDSymbol' (src, tgt) syms node = do
  guard $ notNull syms
  src_arr <- arrow node src
  let src_node = target src_arr
  guard $ locate (root src_node) tgt == Inner
  guard $ nondecomposable src_node tgt
  guard $
    src_node
    |> symbols
    |> filter (/= tgt)
    |> (syms ++)
    |> anySame
    |> not

  let arrSS = arrow2 node .> fromJust .> snd
  let joinSS ss1 ss2 = (fst ss1, symbol (arrSS ss1 `join` arrSS ss2))
  let tgt' = (base, src) `joinSS` (src, tgt) |> snd
  let angs = node |> findValidCoanglesAngles src tgt' |> fromJust
  let src_alts =
        fst angs
        |> fmap ((findIndex \(ss1, ss2) -> ss1 `joinSS` (src, tgt) == ss2) .> fromJust)
  let tgt_alts =
        snd angs
        |> fmap ((findIndex \(ss1, ss2) -> (src, tgt) `joinSS` ss1 == ss2) .> fromJust)

  node <- (node, filter (/= tgt) syms) |> foldlMUncurry \(node, sym) ->
    node |> addNDSymbol src tgt' sym src_alts tgt_alts

  if tgt `elem` syms
  then return node
  else node |> removeNDSymbol (src, tgt)

{- |
Duplicate a node (duplicate an object).

Examples:

>>> printBAC $ fromJust $ duplicateNode 3 (makeSplitter crescent [0,1]) crescent
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4; 9->7; 13->7
  - 0->1; 1->2; 2->9
    &0
    - 0->1
      &1
    - 0->2
      &2
  - 0->3; 1->2; 2->9
    &3
    - 0->1
      *1
    - 0->2
      *2
  - 0->5; 1->6; 2->13
    *0
  - 0->7; 1->6; 2->13
    *3
-}
duplicateNode :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateNode tgt splitter node = do
  guard $ locate (root node) tgt |> (== Inner)
  let arrs = arrowsUnder tgt node
  guard $
    arrs
    |> concatMap (\arr ->
      arr
      |> dict
      |> Map.toList
      |> filter (snd .> (== tgt))
      |> fmap (fst .> (symbol arr,) .> splitter .> length)
    )
    |> allSame
  guard $
    arrs
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> fmap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  fromInner $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {dict = duplicated_dict, target = res}
      where
      duplicate (s, r)
        | dict curr ! r == tgt = splitter (symbol (curr `join` edge), s) `zip` splitter (symbol curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      let splitted_syms = splitter (symbol curr, symbol edge)
      sym <- splitted_syms
      let splitted_dict = dict edge |> Map.insert base sym
      return edge {dict = splitted_dict}

duplicateNodeMutation :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> [Mutation]
duplicateNodeMutation tgt splitter node = incoming_mutation ++ outgoing_mutation
  where
  incoming_mutation =
    suffix node tgt
    |> fmap symbol2
    |> fmap \(s1, s2) ->
      splitter (s1, s2)
      |> fmap (s1,)
      |> Duplication (s1, s2)
  outgoing_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      splitter (tgt, s)
      |> fmap (,s)
      |> Duplication (tgt, s)

{- |
Duplicate a node step by step (duplicate an object step by step).

Examples:

>>> printBAC $ fromJust $ duplicateNode' 3 (makeSplitter crescent [0,1]) crescent
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4; 9->7; 13->7
  - 0->1; 1->2; 2->9
    &0
    - 0->1
      &1
    - 0->2
      &2
  - 0->3; 1->2; 2->9
    &3
    - 0->1
      *1
    - 0->2
      *2
  - 0->5; 1->6; 2->13
    *0
  - 0->7; 1->6; 2->13
    *3
-}
duplicateNode' :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateNode' tgt splitter node = do
  guard $ locate (root node) tgt |> (== Inner)
  let arrs = arrowsUnder tgt node
  guard $
    arrs
    |> concatMap (\arr ->
      arr
      |> dict
      |> Map.toList
      |> filter (snd .> (== tgt))
      |> fmap (fst .> (symbol arr,) .> splitter .> length)
    )
    |> allSame
  guard $
    arrs
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> fmap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  let tgt_subarr = arrow node tgt |> fromJust
  let dup_list = suffixND node tgt |> fmap symbol2
  let split_list =
        node
        |> arrowsUnder tgt
        |> concatMap (\arr -> arr `divide` tgt_subarr |> fmap (arr,))
        |> fmap symbol2
        |> filter (`notElem` dup_list)

  let origin_node = node

  node <- (node, dup_list) |> foldlMUncurry \(node, (s1, s2)) -> do
    let syms = splitter (s1, s2)
    node |> duplicateNDSymbol' (s1, s2) syms

  (node, split_list) |> foldlMUncurry \(node, (s1, s2)) -> do
    let src_arr_origin = arrow origin_node s1 |> fromJust
    let splitted_prefixes =
          prefix (target src_arr_origin) s2
          |> fmap (\(a1, a2) ->
            splitter (symbol (src_arr_origin `join` a1), symbol a2)
            |> fmap (symbol a1,)
          )
          |> transpose

    let src_arr = arrow node s1 |> fromJust
    let splitted_symbols = splitter (s1, s2)

    let syms =
          partitionPrefix (target src_arr) s2
          |> fmap head
          |> fmap \splittable_prefix ->
            splitted_prefixes
            |> findIndex (elem splittable_prefix)
            |> fromJust
            |> (splitted_symbols !!)

    node |> splitSymbol (s1, s2) syms

-- | Duplicate a nondecomposable symbol in the root node (duplicate an initial
--   nondecomposable morphism).
duplicateRootNDSymbol :: Symbol -> [Symbol] -> BAC -> Maybe BAC
duplicateRootNDSymbol tgt = duplicateNDSymbol (base, tgt)

duplicateRootNDSymbolMutation :: Symbol -> [Symbol] -> BAC -> [Mutation]
duplicateRootNDSymbolMutation tgt = duplicateNDSymbolMutation (base, tgt)

-- | Duplicate a leaf node (duplicate a nondecomposable terminal morphism).
duplicateLeafNode :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> Maybe BAC
duplicateLeafNode tgt splitter node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null
  duplicateNode tgt splitter node

duplicateLeafNodeMutation :: Symbol -> ((Symbol, Symbol) -> [Symbol]) -> BAC -> [Mutation]
duplicateLeafNodeMutation = duplicateNodeMutation

{- |
Merge symbols on a node (merge non-terminal morphisms).

Examples:

>>> printBAC $ fromJust $ mergeSymbols (1,[2,3,6,8]) 2 torus
- 0->1; 1->2; 2->3; 4->5; 7->2; 10->5
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->4; 1->2; 2->2
    &2
    - 0->1
      *1
    - 0->2
      *1
  - 0->7; 1->2; 2->2
    *0
  - 0->10; 1->2; 2->2
    *2
-}
mergeSymbols ::
  (Symbol, [Symbol])  -- ^ The symbol referencing the node and symbols to be merged.
  -> Symbol           -- ^ The new symbol after merging.
  -> BAC
  -> Maybe BAC
mergeSymbols (src, tgts) sym node = do
  guard $ notNull tgts
  src_arr <- arrow node src
  tgt_arrs <- tgts |> traverse (arrow (target src_arr))
  guard $ src_arr |> target |> symbols |> filter (`notElem` tgts) |> notElem sym
  guard $ tgt_arrs |> fmap (dict .> Map.delete base) |> allSame
  guard $
    src /= base
    || (tgt_arrs |> fmap (target .> edges .> fmap dict) |> allSame)
  guard $ suffix node src |> all \(_, edge) -> tgts |> fmap (dict edge !) |> allSame

  let merge s = if s `elem` tgts then sym else s

  let res0 = fromEdges do
        edge <- target src_arr |> edges
        let dict' = dict edge |> Map.toList |> fmap (second merge) |> Map.fromList
        return edge {dict = dict'}

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = dict', target = res0}
      where
      dict' = dict edge |> Map.toList |> fmap (first merge) |> Map.fromList

mergeSymbolsMutation :: (Symbol, [Symbol]) -> Symbol -> BAC -> [Mutation]
mergeSymbolsMutation (src, tgts) sym node =
  [Contraction (fmap (src,) tgts) (src, sym)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node (head tgts)
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Contraction (fmap (,s) tgts) (sym, s)

mergeRootSymbols :: [Symbol] -> Symbol -> BAC -> Maybe BAC
mergeRootSymbols tgts = mergeSymbols (base, tgts)

mergeRootSymbolsMutation :: [Symbol] -> Symbol -> BAC -> [Mutation]
mergeRootSymbolsMutation tgts = mergeSymbolsMutation (base, tgts)

{- |
Merge nodes (merge terminal morphisms).

Examples:

>>> crescent' = fromJust $ relabel 2 (fromList [(0,0),(1,2)]) crescent
>>> printBAC $ fromJust $ mergeNodes [2,4] [[False,True], [False,True]] crescent'
- 0->1; 1->2; 2->3; 5->2; 6->3
  - 0->1; 1->2; 2->2
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->5; 1->6; 2->6
    *0
-}
mergeNodes ::
  Eq k
  => [Symbol]   -- ^ The symbols referencing the nodes to be merged.
  -> [[k]]      -- ^ The merging table of nondecomposable incoming morphisms of the nodes.
                --   The arrows with the same key will be merged.
  -> BAC
  -> Maybe BAC
mergeNodes tgts keys node = do
  guard $ notNull tgts
  guard $ lowerIso tgts keys node

  let tgt = head tgts
  let tgt_nodes = tgts |> fmap (arrow node .> fromJust .> target)
  merged_node <- mergeRootNodes tgt_nodes

  let tgt_pars = tgts |> fmap (suffixND node)
  let merging_arrs =
        keys
        |> fmap (fmap ((`elemIndex` head keys) .> fromJust))
        |> zip tgt_pars
        |> fmap (uncurry zip .> sortOn snd .> fmap fst)
        |> transpose

  let nd_merged_dicts = Map.fromList do
        arr_arrs <- merging_arrs
        let merged_wire =
              arr_arrs |> head |> snd |> symbol |> (base,)
        let merged_dict =
              arr_arrs
              |> concatMap (snd .> dict .> Map.delete base .> Map.toList)
              |> (merged_wire :)
              |> Map.fromList
        key <- arr_arrs |> fmap symbol2
        return (key, merged_dict)

  let find_merged_dict (arr1, arr23) =
        suffixND (target arr1) (symbol arr23)
        |> head
        |> \(arr2, arr3) ->
          (arr1 `join` arr2, arr3)
          |> symbol2
          |> (`Map.lookup` nd_merged_dicts)
          |> fromJust
          |> cat (dict arr2)

  fromReachable node $
    node |> foldUnder tgt \curr results ->
      let collapsed_edges = do
            (res, edge) <- results `zip` edges (target curr)
            let is_tgt = symbol (curr `join` edge) `elem` tgts
            let collapsed_node =
                  if is_tgt
                  then merged_node
                  else res |> fromInner |> fromMaybe (target edge)
            let collapsed_dict =
                  if is_tgt
                  then find_merged_dict (curr, edge)
                  else dict edge |> Map.filter (\sym -> dict curr ! sym `notElem` tail tgts)
            return edge {dict = collapsed_dict, target = collapsed_node}

      in fromEdges collapsed_edges

{- |
Merge root nodes (merge BACs).

Examples:

>>> printBAC $ fromJust $ mergeRootNodes [fromJust $ singleton 1, fromJust $ singleton 2, empty, fromJust $ singleton 3]
- 0->1
- 0->2
- 0->3

>>> printBAC $ fromJust $ mergeRootNodes [fromJust $ singleton 6, crescent]
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
- 0->6
-}
mergeRootNodes :: [BAC] -> Maybe BAC
mergeRootNodes nodes = do
  guard $ nodes |> fmap (symbols .> filter (/= base)) |> concat |> anySame |> not
  return $ nodes |> concatMap edges |> fromEdges

-- | Remove a node (remove initial and terminal morphisms simultaneously).
removeNode :: Symbol -> BAC -> Maybe BAC
removeNode tgt node = do
  guard $ locate (root node) tgt == Inner
  tgt_arr <- arrow node tgt
  guard $ missingAltPathsOfNode tgt node == Just []

  fromReachable (target tgt_arr) $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtBoundary -> mzero
    AtInner res -> return edge {dict = filtered_dict, target = res}
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

removeNodeMutation :: Symbol -> BAC -> [Mutation]
removeNodeMutation tgt node =
  arrow node tgt
  |> fromJust
  |> target
  |> edges
  |> fmap symbol
  |> fmap (tgt,)
  |> fmap Deletion
  |> (++) (
    suffix node tgt
    |> fmap symbol2
    |> fmap Deletion
  )

appendNode :: Symbol -> BAC -> Maybe BAC
appendNode src node = do
  src_arr <- arrow node src
  let src_node = target src_arr
  let new_node = fromJust $ singleton (maximum (symbols src_node) + 1)
  let res0 = fromJust $ mergeRootNodes [src_node, new_node]
  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) lres -> case fromReachable res0 lres of
      Nothing -> return edge
      Just res -> return edge {dict = new_dict, target = res}
        where
        new_sym = symbols (target curr) |> maximum |> (+ 1)
        new_sym' = symbols (target edge) |> maximum |> (+ 1)
        new_dict = dict edge |> Map.insert new_sym' new_sym

insertNode :: (Symbol, Maybe Symbol) -> BAC -> Maybe BAC
insertNode (src, tgt) node = do
  src_arr <- arrow node src
  let new_sym = target src_arr |> symbols |> maximum |> (+ 1)
  new_inedge <- case tgt of
    Just tgt -> do
      guard $ tgt /= base
      tgt_arr <- arrow (target src_arr) tgt
      let new_outdict = target tgt_arr |> symbols |> fmap (\s -> (s, s+1)) |> Map.fromList
      let new_outedge = Arrow {dict = new_outdict, target = target tgt_arr}
      let new_node = fromEdges [new_outedge]
      let new_indict = dict tgt_arr |> Map.mapKeys (+ 1) |> Map.insert base new_sym
      return Arrow {dict = new_indict, target = new_node}
    Nothing ->
      return Arrow {dict = Map.singleton base new_sym, target = empty}

  let res0 = fromEdges $ edges (target src_arr) ++ [new_inedge]

  fromReachable res0 $ node |> modifyUnder src \(curr, edge) res ->
    case fromReachable res0 res of
      Nothing -> return edge
      Just res -> return edge {dict = dict', target = res}
        where
        newSym syms = (+) (maximum syms + 1)
        s_syms = target curr |> symbols
        r_syms = target edge |> symbols
        dict' =
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if dict curr ! r == src
            then [(s, r), (newSym s_syms s, newSym r_syms r)]
            else [(s, r)]
          )
          |> Map.fromList

expandMergingSymbols :: BAC -> [[Symbol]] -> [[Symbol]]
expandMergingSymbols node =
  fmap (fmap (arrow node .> fromJust .> dict .> Map.toList))
  .> zip [0 :: Integer ..]
  .> concatMap sequence
  .> concatMap sequence
  .> fmap (\(a, (b, c)) -> ((a, b), c))
  .> bipartiteEqclass
  .> fmap snd
  .> filter (length .> (> 1))
  .> fmap sort
  .> sort

mergeSymbolsAggressively :: Symbol -> [[Symbol]] -> BAC -> Maybe BAC
mergeSymbolsAggressively src tgts node = do
  src_arr <- arrow node src

  tgt_arrs <- tgts |> traverse (traverse (arrow (target src_arr)))
  guard $ tgt_arrs |> all (fmap target .> allSame)

  let mergeSymbol tgts' s = tgts' |> find (elem s) |> fmap head |> fromMaybe s

  let merging_lists = expandMergingSymbols (target src_arr) tgts
  let merged_node = fromEdges do
        arr <- target src_arr |> edges
        let merged_dict = dict arr |> fmap (mergeSymbol merging_lists)
        return arr {dict = merged_dict}
  let res0 = (merged_node, merging_lists)

  lres <- sequence $
    node |> foldUnder src \curr results -> do
      results' <- traverse sequence results
      let merging_lists_of = fromReachable res0 .> fmap snd .> fromMaybe []
      let merging_lists =
            results'
            |> concatMap merging_lists_of
            |> zip (target curr |> edges |> fmap dict)
            |> fmap (sequence .> fmap (uncurry (!)))
            |> expandMergingSymbols (target curr)
      let merged_node = fromEdges do
            (lres, edge) <- results' `zip` edges (target curr)
            let merged_dict =
                  dict edge
                  |> fmap (mergeSymbol merging_lists)
                  |> Map.mapKeys (mergeSymbol (merging_lists_of lres))
            case fromReachable res0 lres of
              Nothing -> return edge {dict = merged_dict}
              Just (res, _) -> return edge {dict = merged_dict, target = res}
      return (merged_node, merging_lists)

  fromReachable merged_node $ fmap fst lres

