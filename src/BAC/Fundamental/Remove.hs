{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Remove (
  removeNDSymbol,
  removeNode,
  removeNDSymbolOnRoot,
  removeLeafNode,
  removePrefix,
  removeSuffix,
) where

import Control.Monad (guard)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map

import BAC.Base
import Utils.Utils ((.>), (|>), guarded)

-- $setup
-- >>> import Data.Tuple.Extra (both)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.Map (fromList)
-- >>> import Data.Maybe (fromJust)
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


{- |
Remove a nondecomposable symbol in a node (remove a non-terminal nondecomposable morphism).

Examples:

>>> printBAC $ fromJust $ removeNDSymbol (1,1) cone
- 0->1
- 0->2
  &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1

>>> printBAC $ fromJust $ removeNDSymbol (0,3) cone
- 0->1; 1->2
  - 0->1
    &0
- 0->4; 1->2; 2->6
  - 0->1
    *0
  - 0->2

>>> printBAC $ cone |> removeNDSymbol (3,1) |> fromJust |> removeNDSymbol (3,4) |> fromJust
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
  (src_arr, tgt_subarr) <- arrow2 node (src, tgt)
  guard $ nondecomposable (target src_arr) tgt

  let res0 = fromEdges do
        edge <- edges (target src_arr)
        if symbol edge /= tgt
        then return edge
        else do
          subedge <- target edge |> edges
          return $ edge `join` subedge

  fromReachable res0 $ node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner res -> return edge {target = res}
    AtBoundary -> [edge {dict = filtered_dict, target = res0}, edge `join` tgt_subarr]
      where
      filtered_dict = dict edge |> Map.delete tgt

-- | Remove a nondecomposable symbol in the root node (remove a nondecomposable initial
--   morphism).
removeNDSymbolOnRoot :: Symbol -> BAC -> Maybe BAC
removeNDSymbolOnRoot tgt = removeNDSymbol (base, tgt)


-- | Remove a node (remove initial and terminal morphisms simultaneously).
removeNode :: Symbol -> BAC -> Maybe BAC
removeNode tgt node = do
  guard $ locate (root node) tgt == Inner
  tgt_arr <- arrow node tgt

  fromReachable (target tgt_arr) $ node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtBoundary -> do
      subedge <- target edge |> edges
      return $ edge `join` subedge
    AtInner res -> return edge {dict = filtered_dict, target = res}
      where
      filtered_dict = dict edge |> Map.filter (\s -> dict curr ! s /= tgt)

-- | Remove a leaf node (remove a nondecomposable terminal morphisms).
removeLeafNode :: Symbol -> BAC -> Maybe BAC
removeLeafNode tgt node = do
  tgt_arr <- arrow node tgt
  guard $ target tgt_arr |> edges |> null

  removeNode tgt node


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
