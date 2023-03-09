{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Braider where

import BAC
import Utils

import Control.Monad (guard)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (foldlM)
import Data.List (nub)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, listToMaybe)
import qualified DAG
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT, MaybeT))
import Control.Monad.Identity (Identity (runIdentity))

-- $setup
-- The examples run with the following settings:
-- 
-- >>> import YAML
-- >>> import Data.Maybe (fromMaybe)

type BraiderT e p m v = DAG.BuilderT (Edge e) (Node e) p (MaybeT m) v

-- | Make a knot in the Braider.  See 'braid'.
knot :: (DAG.Pointer p, Monad m) => [(e, p)] -> BraiderT e p m p
knot ptrs = do
  table <- DAG.getTable

  let node =
        ptrs
        |> fmap (second ((table !) .> fst))
        |> zip [1..]
        |> fmap (\(num, (eval, subnode)) ->
          subnode
          |> symbols
          |> fmap (\a -> (a, relabel ((if a == base then [num, 0] else [num]) ++) a))
          |> Map.fromList
          |> \dict -> Arrow {dict = dict, node = subnode, value = eval}
        )
        |> \edges -> Node {edges = edges}

  let children = ptrs |> zip (edges node) |> fmap (fmap snd)

  DAG.node node children

-- | Make a knot without value in the Braider.  See 'braid'.
knot' :: (DAG.Pointer p, Monad m) => [p] -> BraiderT () p m p
knot' ptrs = knot (fmap ((),) ptrs)

-- | Merge symbols in the Braider.  See 'braid'.
infixl 4 //
(//) :: (DAG.Pointer p, Monad m) => BraiderT e p m p -> [[Int]] -> BraiderT e p m p
braiding // eqclass = do
  p <- braiding
  table <- DAG.getTable
  let (node, children) = table ! p

  let pathToPointer =
        foldlM
        (\p index -> p |> (table !) |> snd |> fmap snd |> drop index |> listToMaybe)
        p

  lift $ MaybeT $ pure $ do
    ptrs <- eqclass |> traverse pathToPointer
    guard $ ptrs |> nub |> length |> (<= 1)
    guard $ ptrs /= [p]

  let pathToArrow = foldl (\arr index -> arr |> next |> (!! index)) (root node)

  let eqclass' =
        eqclass
        |> fmap (pathToArrow .> symbolize)
        |> (: [])
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

-- | Make a BAC by a monad-typed builder.  See 'braid'.
braidM :: Monad m => (forall p. DAG.Pointer p => BraiderT e p m p) -> m (Maybe (Node e))
braidM braiding = DAG.buildM braiding |> runMaybeT |> fmap (fmap DAG.value)

{- | Make a BAC by a monad-typed builder.

Examples:

>>> :{
let cone = braid $ do
      y <- knot' []
      b <- knot' []
      p <- knot' [y]
      c <- knot' [y, b]
      v <- knot' [c, c] // [[0,0], [1,0]] // [[0,1], [1,1]]
      knot' [p, v] // [[1,0], [1,1]] // [[0,0], [1,0,0]]
in  putStrLn $ cone |> fmap encodeNode' |> fromMaybe "Nothing"
:}
- dict: '$=$1.0; $1.0=$1.1.0'
  node:
    - dict: '$=$1.0'
      node: &0 []
- dict: '$=$2.0; $1.0=$2.1.0; $1.1.0=$1.1.0; $1.2.0=$2.1.2.0; $2.0=$2.1.0'
  node:
    - dict: '$=$1.0; $1.0=$1.1.0; $2.0=$1.2.0'
      node: &1
        - dict: '$=$1.0'
          node: *0
        - dict: '$=$2.0'
          node: []
    - dict: '$=$2.0; $1.0=$1.1.0; $2.0=$1.2.0'
      node: *1
<BLANKLINE>

>>> :{
let torus = braid $ do
      t <- knot' []
      c <- knot' [t, t]
      c' <- knot' [t, t]
      p <- knot' [c, c', c, c']
        // [[0,1], [1,0]]
        // [[1,1], [2,1]]
        // [[2,0], [3,1]]
        // [[3,0], [0,0]]
      knot' [p]
        // [[0,0], [0,2]]
        // [[0,1], [0,3]]
in  putStrLn $ torus |> fmap encodeNode' |> fromMaybe "Nothing"
:}
- dict: '$=$1.0; $1.0=$1.1.0; $1.1.0=$1.1.1.0; $1.2.0=$1.1.1.0; $2.0=$1.2.0; {- LINEBREAK
        -}$2.2.0=$1.1.1.0; $3.0=$1.1.0; $3.1.0=$1.1.1.0; $4.0=$1.2.0'
  node:
    - dict: '$=$1.0; $1.0=$1.1.0; $2.0=$1.2.0'
      node: &0
        - dict: '$=$1.0'
          node: &1 []
        - dict: '$=$2.0'
          node: *1
    - dict: '$=$2.0; $1.0=$1.2.0; $2.0=$2.2.0'
      node: &2
        - dict: '$=$1.0'
          node: *1
        - dict: '$=$2.0'
          node: *1
    - dict: '$=$3.0; $1.0=$3.1.0; $2.0=$2.2.0'
      node: *0
    - dict: '$=$4.0; $1.0=$1.1.0; $2.0=$3.1.0'
      node: *2
<BLANKLINE>
-}
braid :: (forall p. DAG.Pointer p => BraiderT e p Identity p) -> Maybe (Node e)
braid braiding = runIdentity (braidM braiding)
