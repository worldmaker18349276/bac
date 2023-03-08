{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Braider where

import BAC

import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (for_, foldlM)
import Data.List (nub)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, listToMaybe)
import qualified DAG
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT, MaybeT))
import Control.Monad.Identity (Identity (runIdentity))

type BraiderT e n p m v = DAG.BuilderT (Edge e n) (Node e n) p (MaybeT m) v

knot :: (DAG.Pointer p, Monad m) => n -> [(e, p)] -> [[[Int]]] -> BraiderT e n p m p
knot value children eqclass = do
  table <- DAG.getTable

  let node =
        children
        |> fmap (second ((table !) .> fst))
        |> zip [0..]
        |> fmap (\(num, (eval, subnode)) ->
          subnode
          |> symbols
          |> fmap (\a -> (a, relabel (num :) a))
          |> Map.fromList
          |> \dict -> Arrow {dict = dict, node = subnode, evalue = eval}
        )
        |> \edges -> Node {edges = edges, nvalue = value}

  let pathToPointer indices = do
        guard $ not (null indices)
        let list !!? i = list |> drop i |> listToMaybe
        p0 <- fmap snd children !!? head indices
        let walk p index = fmap snd (snd (table ! p)) !!? index
        foldlM walk p0 (tail indices)

  lift $ MaybeT $ pure $ for_ eqclass $ \rels -> do
    ptrs <- rels |> traverse pathToPointer
    guard $ ptrs |> nub |> length |> (<= 1)

  let pathToArrow indices =
        foldl
        (next .> (!!))
        (head indices |> (edges node !!) |> asArrow)
        (tail indices)

  let eqclass' =
        eqclass
        |> fmap (fmap (pathToArrow .> symbolize))
        |> expandMergingSymbols node
        |> fromJust

  let mergeSymbol sym = eqclass' |> filter (elem sym) |> (++ [[sym]]) |> head |> head
  let merged_edges = do
        edge <- edges node
        let merged_dict = dict edge |> fmap mergeSymbol
        let merged_edge = edge {dict = merged_dict}
        [merged_edge]
  let merged_node = node {edges = merged_edges}
  let merged_children = children |> zip (edges merged_node) |> fmap (fmap snd)

  DAG.node merged_node merged_children

braidM
  :: Monad m => (forall p. DAG.Pointer p => BraiderT e n p m p) -> m (Maybe (Node e n))
braidM braiding =
  DAG.buildM braiding |> runMaybeT |> fmap (fmap DAG.value)

braid :: (forall p. DAG.Pointer p => BraiderT e n p Identity p) -> Maybe (Node e n)
braid braiding = runIdentity (braidM braiding)

{-
cone :: Maybe (Node Int String)
cone = braid $ do
  y <- knot "side" [] []
  b <- knot "bottom" [] []
  p <- knot "tip" [(2, y)] []
  c <- knot "circle" [(1, y), (-1, b)] []
  v <- knot "point" [(1, c), (-1, c)]
    [
      [[0,0], [1,0]],
      [[0,1], [1,1]]
    ]
  knot "void" [(1, p), (1, v)]
    [
      [[1,0], [1,1]],
      [[0,0], [1,0,0]]
    ]

torus :: Maybe (Node Int String)
torus = braid $ do
  t <- knot "torus" [] []
  c <- knot "circle" [(1, t), (-1, t)] []
  c' <- knot "circle'" [(1, t), (-1, t)] []
  p <- knot "intersected point" [(1, c), (1, c'), (-1, c), (-1, c')]
    [
      [[0,1], [1,0]],
      [[1,1], [2,1]],
      [[2,0], [3,1]],
      [[3,0], [0,0]]
    ]
  knot "void" [(1, p)]
    [
      [[0,0], [0,2]],
      [[0,1], [0,3]]
      -- induced: [[0,0,0], [0,1,0], [0,2,0], [0,3,0], [0,0,1], [0,1,1], [0,2,1], [0,3,1]]
    ]
-}
