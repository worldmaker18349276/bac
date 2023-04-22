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
  removeLeafNode,

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
  makeInserter,
  addLeafNode,
  addParentNode,
  addParentNodeOnRoot,

  addNDSymbolMutation,
  addLeafNodeMutation,
  addParentNodeMutation,
  addParentNodeOnRootMutation,

  -- * Duplicate Symbol, Node

  duplicateNDSymbol,
  duplicateNode,
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
  mergeLeafNodes,
  mergeRootNodes,

  mergeSymbolsMutation,
  mergeRootSymbolsMutation,
  mergeNodesMutation,
  mergeLeafNodesMutation,
) where

import Control.Arrow ((&&&))
import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first, second, bimap))
import Data.Foldable (find)
import Data.Foldable.Extra (notNull)
import Data.List (elemIndices, findIndex, nub, sort)
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
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Examples (cone, torus, crescent)

-- | A mark indicating mutations of symbols.
data Mutation =
    Transfer  [(Symbol, Symbol)] [(Symbol, Symbol)]
  | Duplicate  (Symbol, Symbol)  [(Symbol, Symbol)]
  | Merge     [(Symbol, Symbol)]  (Symbol, Symbol)
  | Delete     (Symbol, Symbol)
  | Insert                        (Symbol, Symbol)

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
addEdgeMutation (src, tgt) _node = [Insert (src, tgt)]

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
removeEdgeMutation (src, tgt) _node = [Delete (src, tgt)]

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
  |> uncurry Transfer
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
      |> uncurry Transfer
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
  [Transfer [(src, tgt)] [(src, sym)] | is_edge]
  |> if src == base then (++ root_mutation) else id
  where
  is_edge =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> elem tgt
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap dupe
    |> fmap ((tgt,) `bimap` (sym,))
    |> unzip
    |> uncurry Transfer
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
        (arr1, arr2) <- suffixND node src
        guard $
          suffix (target arr1) (symbol (arr2 `join` tgt_arr))
          |> all (first (join arr1) .> symbol2 .> (== (src, tgt)))
        return $ symbol2 (arr1, arr2 `join` tgt_arr)
  let tgt_alts = nubSort do
        arr <- edgesND (target tgt_arr)
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
  let outedges = edgesND (target src_arr)
  (arr1, arr2) <- suffixND node src
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
  src_node <- arrow node src |> fmap target
  guard $ nondecomposable src_node tgt
  guard $ missingAltPathsOfArrow (src, tgt) node == Just ([],[])

  let res0 = src_node |> edges |> filter (\edge -> symbol edge /= tgt) |> fromEdges
  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> return edge {dict = filtered_dict, target = res0}
      where
      filtered_dict = dict edge |> Map.delete tgt

removeNDSymbolMutation :: (Symbol, Symbol) -> BAC -> [Mutation]
removeNDSymbolMutation (src, tgt) node =
  [Delete (src, tgt)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap (tgt,)
    |> fmap Delete

-- | Remove a nondecomposable symbol in the root node (remove a nondecomposable initial
--   morphism).
removeRootNDSymbol :: Symbol -> BAC -> Maybe BAC
removeRootNDSymbol tgt = removeNDSymbol (base, tgt)

removeRootNDSymbolMutation :: Symbol -> BAC -> [Mutation]
removeRootNDSymbolMutation tgt = removeNDSymbolMutation (base, tgt)


-- | Remove a leaf node (remove a nondecomposable terminal morphisms).
removeLeafNode :: Symbol -> BAC -> Maybe BAC
removeLeafNode tgt node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null

  removeNode tgt node

removeLeafNodeMutation :: Symbol -> BAC -> [Mutation]
removeLeafNodeMutation = removeNodeMutation


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
  [Insert (src, sym)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Duplicate (tgt, s) [(tgt, s), (sym, s)]

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
  [Duplicate (src, tgt) (fmap (src,) syms) | is_edge]
  |> if src == base then (++ root_mutation) else id
  where
  is_edge =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> elem tgt
  syms = nub splitted_syms
  splittable_groups = arrow node src |> fromJust |> target |> (`partitionPrefix` tgt)
  splitted_groups =
    splitted_syms `zip` splittable_groups
    |> groupOnKey fst
    |> fmap (second (concatMap snd))
  root_mutation =
    splitted_groups
    |> fmap \(sym, group) ->
      Transfer group (fmap (first (const sym)) group)

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
      Duplicate (s1, s2) (splitter (s1, s2) |> Map.elems |> fmap (s1,))
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
    |> uncurry Transfer
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
  [Duplicate (src, tgt) (fmap (src,) syms)]
  |> if src == base then (++ root_mutation) else id
  where
  root_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      Duplicate (tgt, s) (fmap (,s) syms)

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
      |> Duplicate (s1, s2)
  outgoing_mutation =
    arrow node tgt
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> fmap \s ->
      splitter (tgt, s)
      |> fmap (,s)
      |> Duplicate (tgt, s)


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
  [Merge (fmap (src,) tgts') (src, sym) | notNull tgts']
  |> if src == base then (++ root_mutation) else id
  where
  tgts' =
    arrow node src
    |> fromJust
    |> target
    |> edges
    |> fmap symbol
    |> filter (`elem` tgts)
  root_mutation =
    tgts
    |> fmap \tgt ->
      arrow node tgt
      |> fromJust
      |> target
      |> edges
      |> fmap symbol
      |> fmap (tgt,) &&& fmap (sym,)
      |> uncurry Transfer

mergeRootSymbols :: [Symbol] -> Symbol -> BAC -> Maybe BAC
mergeRootSymbols tgts = mergeSymbols (base, tgts)

mergeRootSymbolsMutation :: [Symbol] -> Symbol -> BAC -> [Mutation]
mergeRootSymbolsMutation tgts = mergeSymbolsMutation (base, tgts)

{- |
Merge nodes (merge terminal morphisms).

Examples:

>>> crescent' = fromJust $ relabel 2 (fromList [(0,0),(1,2)]) crescent
>>> printBAC $ fromJust $ mergeNodes [(2,[False,True]),(4,[False,True])] (snd .> head) crescent'
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
  Ord k
  => [(Symbol, [k])]   -- ^ The symbols referencing the nodes to be merged and the keys to
                       --   classify nondecomposable incoming morphisms.
  -> ((Symbol, [Symbol]) -> Symbol)
                       -- ^ The merger of symbols.
  -> BAC
  -> Maybe BAC
mergeNodes tgts_keys merger node = do
  guard $ notNull tgts_keys
  guard $ tgts_keys |> fmap fst |> anySame |> not

  zipped_suffix <- zipSuffix tgts_keys node
  guard $
    zipped_suffix
    |> groupSortOn (fst .> symbol)
    |> fmap ((head .> fst) &&& fmap snd)
    |> all \(curr, groups) ->
      let
        sym0 = symbol curr
        syms = groups |> concat |> fmap symbol
        syms' = groups |> fmap (fmap symbol .> (sym0,) .> merger)
      in
        curr
        |> target
        |> symbols
        |> filter (`notElem` syms)
        |> (++ syms')
        |> anySame
        |> not

  let tgts = tgts_keys |> fmap fst
  let tgt_nodes = tgts |> fmap (arrow node .> fromJust .> target)
  merged_node <- mergeRootNodes tgt_nodes

  let merged_syms_dicts = Map.fromList do
        (curr, arrs) <- zipped_suffix
        let sym0 = symbol curr
        let syms = fmap symbol arrs
        let sym' = merger (sym0, syms)
        let merged_dict =
              arrs
              |> fmap dict
              |> foldl Map.union Map.empty
              |> Map.insert base sym'
        sym <- syms
        return ((sym0, sym), (sym', merged_dict))

  fromReachable node $
    node |> foldUnder (head tgts) \curr results -> fromEdges do
      (res, edge) <- results `zip` edges (target curr)
      let sym0 = symbol curr
      let sym = symbol (curr `join` edge)
      let collapsed_node =
            if sym `elem` tgts
            then merged_node
            else res |> fromInner |> fromMaybe (target edge)
      let collapsed_dict =
            if sym `elem` tgts
            then snd (merged_syms_dicts ! (sym0, symbol edge))
            else
              dict edge
              |> Map.toList
              |> fmap (\(s1, s2) ->
                (
                  Map.lookup (sym, s1) merged_syms_dicts |> maybe s1 fst,
                  Map.lookup (sym0, s2) merged_syms_dicts |> maybe s2 fst
                )
              )
              |> Map.fromList
      return edge {dict = collapsed_dict, target = collapsed_node}

mergeNodesMutation ::
  Ord k => [(Symbol, [k])] -> ((Symbol, [Symbol]) -> Symbol) -> BAC -> [Mutation]
mergeNodesMutation tgts_keys merger node = incoming_mutation ++ outgoing_mutation
  where
  tgts = tgts_keys |> fmap fst
  tgt_suffix = suffix node (head tgts) |> fmap symbol2
  zipped_suffix =
    zipSuffix tgts_keys node
    |> fromJust
    |> fmap (symbol `bimap` fmap symbol)
    |> filter (second head .> (`elem` tgt_suffix))
  incoming_mutation =
    zipped_suffix
    |> fmap (sequence &&& (fst &&& merger))
    |> fmap (uncurry Merge)
  outgoing_mutation =
    tgts
    |> concatMap (\tgt ->
      arrow node tgt
      |> fromJust
      |> target
      |> edges
      |> fmap (symbol .> (tgt,))
    )
    |> \old_edges ->
      old_edges
      |> fmap (first (const (merger (base, tgts))))
      |> Transfer old_edges
      |> (: [])

mergeLeafNodes ::
  Ord k => [(Symbol, [k])] -> ((Symbol, [Symbol]) -> Symbol) -> BAC -> Maybe BAC
mergeLeafNodes tgts_keys merger node = do
  tgt_nodes <- tgts_keys |> fmap fst |> traverse (arrow node .> fmap target)
  guard $ tgt_nodes |> all (edges .> null)
  mergeNodes tgts_keys merger node

mergeLeafNodesMutation ::
  Ord k => [(Symbol, [k])] -> ((Symbol, [Symbol]) -> Symbol) -> BAC -> [Mutation]
mergeLeafNodesMutation = mergeNodesMutation

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
  |> fmap Delete
  |> (++) (
    suffix node tgt
    |> fmap symbol2
    |> fmap Delete
  )

addLeafNode :: Symbol -> (Symbol -> Symbol) -> BAC -> Maybe BAC
addLeafNode src inserter node = do
  src_arr <- arrow node src
  let src_node = target src_arr
  let sym = inserter src
  guard $ sym `notElem` symbols src_node
  guard $
    arrowsUnder src node |> all \curr ->
      target curr |> symbols |> notElem (inserter (symbol curr))

  let new_node = fromJust $ singleton sym
  let res0 = fromJust $ mergeRootNodes [src_node, new_node]
  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) lres -> case fromReachable res0 lres of
      Nothing -> return edge
      Just res -> return edge {dict = new_dict, target = res}
        where
        new_sym = inserter (symbol curr)
        new_sym' = inserter (symbol (curr `join` edge))
        new_dict = dict edge |> Map.insert new_sym' new_sym

addLeafNodeMutation :: Symbol -> (Symbol -> Symbol) -> BAC -> [Mutation]
addLeafNodeMutation src inserter _node = [Insert (src, inserter src)]

makeInserter :: BAC -> (Symbol, Symbol) -> Symbol
makeInserter node (src, tgt) =
  arrow node src |> fromJust |> target |> symbols |> maximum |> (+ tgt)

addParentNode ::
  (Symbol, Symbol) -> Symbol -> ((Symbol, Symbol) -> Symbol) -> BAC -> Maybe BAC
addParentNode (src, tgt) tgt' inserter node = do
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let tgt_arr = src_arr `join` tgt_subarr
  guard $ tgt /= base

  let sym = inserter (src, tgt)
  guard $ tgt' `notElem` symbols (target tgt_subarr)
  guard $ sym `notElem` symbols (target src_arr)
  guard $
    arrowsUnder src node |> all \curr ->
      curr `divide` tgt_arr
      |> fmap (symbol .> (symbol curr,) .> inserter)
      |> (++ symbols (target curr))
      |> anySame
      |> not

  let new_outdict =
        target tgt_subarr |> symbols |> fmap dupe |> Map.fromList |> Map.insert base tgt'
  let new_outedge = Arrow {dict = new_outdict, target = target tgt_subarr}
  let new_node = fromEdges [new_outedge]
  let new_indict = dict tgt_subarr |> Map.insert tgt' sym
  let new_inedge = Arrow {dict = new_indict, target = new_node}
  let res0 = fromEdges $ edges (target src_arr) `snoc` new_inedge

  fromReachable res0 $
    node |> modifyUnder src \(curr, edge) lres -> case fromReachable res0 lres of
      Nothing -> return edge
      Just res -> return edge {dict = dict', target = res}
        where
        sym0 = symbol curr
        sym = symbol (curr `join` edge)
        dict' =
          dict edge
          |> Map.toList
          |> concatMap (\(s, r) ->
            if dict curr ! r == tgt
            then [(s, r), (inserter (sym, s), inserter (sym0, r))]
            else [(s, r)]
          )
          |> Map.fromList

addParentNodeMutation ::
  (Symbol, Symbol) -> Symbol -> ((Symbol, Symbol) -> Symbol) -> BAC -> [Mutation]
addParentNodeMutation (src, tgt) tgt' inserter node =
  [Insert (src, sym), Insert (sym', tgt')]
  where
  sym = inserter (src, tgt)
  src_tgt = (src, tgt) |> arrow2 node |> fromJust |> uncurry join |> symbol
  sym' = inserter (base, src_tgt)

addParentNodeOnRoot :: Symbol -> Symbol -> Symbol -> BAC -> Maybe BAC
addParentNodeOnRoot tgt tgt' sym = addParentNode (base, tgt) tgt' (const sym)

addParentNodeOnRootMutation :: Symbol -> Symbol -> Symbol -> BAC -> [Mutation]
addParentNodeOnRootMutation tgt tgt' sym =
  addParentNodeMutation (base, tgt) tgt' (const sym)
