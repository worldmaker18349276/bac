{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Remove (
  missingAltPathsOfArrow,
  missingAltPathsOfNode,
  removeNDSymbol,
  removeNode,
  removeNDSymbolOnRoot,
  removeLeafNode,
  removePrefix,
  removeSuffix,

  removeNDSymbolMutation,
  removeNodeMutation,
  removeNDSymbolOnRootMutation,
  removeLeafNodeMutation,
) where

import Control.Monad (MonadPlus (mzero), guard)
import Data.Bifunctor (Bifunctor (first))
import Data.List.Extra (nubSort)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

import BAC.Base
import BAC.Fundamental.Mutation
import Utils.Utils ((.>), (|>), guarded)

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


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
removeNDSymbolOnRoot :: Symbol -> BAC -> Maybe BAC
removeNDSymbolOnRoot tgt = removeNDSymbol (base, tgt)

removeNDSymbolOnRootMutation :: Symbol -> BAC -> [Mutation]
removeNDSymbolOnRootMutation tgt = removeNDSymbolMutation (base, tgt)


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

-- | Remove a leaf node (remove a nondecomposable terminal morphisms).
removeLeafNode :: Symbol -> BAC -> Maybe BAC
removeLeafNode tgt node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null

  removeNode tgt node

removeLeafNodeMutation :: Symbol -> BAC -> [Mutation]
removeLeafNodeMutation = removeNodeMutation


removePrefix :: (Symbol, Symbol) -> BAC -> Maybe BAC
removePrefix (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  let src_node = target src_arr
  let remove_list = arrowsUnder src_node tgt |> fmap symbol |> filter (/= base) |> (tgt :)

  let res0 =
        target src_arr
        |> edges
        |> filter (dict .> notElem tgt)
        |> fromEdges
  let syms0 = symbols res0
  guard $ symbols src_node |> filter (`notElem` remove_list) |> (== syms0)

  fromReachable res0 $
    node |> modifyUnder src \(_curr, edge) -> \case
      AtOuter -> return edge
      AtInner res -> return edge {target = res}
      AtBoundary -> return edge {dict = dict', target = res0}
        where
        dict' = dict edge |> Map.filterWithKey \s _ -> s `elem` syms0

removeSuffix :: (Symbol, Symbol) -> BAC -> Maybe BAC
removeSuffix (src, tgt) node = do
  guard $ tgt /= base
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  let tgt_arr = src_arr `join` tgt_subarr
  let tgt' = symbol tgt_arr
  let tgt_node = target tgt_subarr

  lres <- sequence $
    node |> foldUnder tgt' \curr results -> do
      let is_outside = null (src_arr `divide` curr)
      let remove_list = if is_outside then [] else curr `divide` tgt_arr |> fmap symbol

      results' <- traverse sequence results

      let res = fromEdges do
            (lres, edge) <- results' `zip` edges (target curr)
            case lres of
              AtOuter -> return edge
              AtBoundary -> guarded (const is_outside) edge
              AtInner res | null (src_arr `divide` (curr `join` edge)) ->
                return edge {target = res}
              AtInner res | null (src_arr `divide` (curr `join` edge)) ->
                return edge {target = res}
              AtInner res -> return edge {dict = dict', target = res}
                where
                dict' = target edge |> symbols |> foldr Map.delete (dict edge)

      guard $ symbols (target curr) |> filter (`notElem` remove_list) |> (== symbols res)

      return res

  fromReachable tgt_node lres
