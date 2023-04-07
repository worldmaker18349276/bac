{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Braider (
  BraiderT,
  knot,
  (//),
  braidM,
  braid,
) where

import BAC.Base
import BAC.Algorithm (expandMergingSymbols)
import Utils.Utils ((|>), (.>))
import qualified Utils.DAG as DAG

import Control.Monad (guard)
import Data.Foldable (foldlM, find)
import Data.List (nub)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, fromMaybe)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT, MaybeT))
import Control.Monad.Identity (Identity (runIdentity))

type BraiderT p m v = DAG.BuilderT Arrow Node p (MaybeT m) v

-- | Make a knot in the Braider.  See 'braid'.
knot :: (DAG.Pointer p, Monad m) => [p] -> BraiderT p m p
knot ptrs = do
  table <- DAG.getTable

  let nums =
        ptrs
        |> fmap ((table !) .> fst .> symbols .> maximum .> (+ 1))
        |> scanl (+) 1
  let node =
        ptrs
        |> fmap ((table !) .> fst)
        |> zip nums
        |> fmap (\(num, subnode) -> Arrow {
            dict = subnode |> symbols |> fmap (\a -> (a, num + a)) |> Map.fromList,
            target = subnode
          }
        )
        |> fromEdges

  let children = ptrs |> zip (edges node)

  DAG.node node children

-- | Merge symbols in the Braider.  See 'braid'.
infixl 2 //
(//) :: (DAG.Pointer p, Monad m) => BraiderT p m p -> [[Int]] -> BraiderT p m p
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

  let pathToArrow = foldl (\arr index -> arr |> extend |> (!! index)) (root node)

  let eqclass' =
        eqclass
        |> fmap (pathToArrow .> symbol)
        |> (: [])
        |> expandMergingSymbols node

  let mergeSymbol sym = eqclass' |> find (elem sym) |> fmap head |> fromMaybe sym
  let merged_edges = do
        arr <- edges node
        let merged_dict = dict arr |> fmap mergeSymbol
        return arr {dict = merged_dict}
  let merged_node = fromEdges merged_edges
  let merged_children = children |> zip (edges merged_node) |> fmap (fmap snd)

  DAG.node merged_node merged_children

-- | Make a BAC by a monad-typed builder.  See 'braid'.
braidM :: Monad m => (forall p. DAG.Pointer p => BraiderT p m p) -> m (Maybe Node)
braidM braiding = DAG.buildM braiding |> runMaybeT |> fmap (fmap DAG.value)

braid :: (forall p. DAG.Pointer p => BraiderT p Identity p) -> Maybe Node
braid braiding = runIdentity (braidM braiding)
