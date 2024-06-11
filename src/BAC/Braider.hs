{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TupleSections #-}

module BAC.Braider (
  BraiderT,
  knot,
  Edge (..),
  Path (..),
  (//),
  braidM,
  braid,
) where

import Control.Applicative (Alternative (empty))
import Control.Monad (guard)
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.State (StateT (runStateT), get, gets, put)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Data.Foldable (find, foldlM)
import Data.List (nub, sort)
import Data.List.Extra ((!?))
import Data.Map.Strict (Map, insert, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import BAC.Base hiding (empty)
import Utils.DisjointSet (bipartiteEqclass)
import Utils.Utils ((.>), (|>))

type DAG e p = Map p (BAC e, [Edge e p])
data BraidState e p = BraidState (DAG e p) [p]

newtype BraiderT e p m v = BraiderT {runBraiderT :: StateT (BraidState e p) (MaybeT m) v}
  deriving (Functor, Applicative, Alternative, Monad)

getTable :: Monad m => BraiderT e p m (DAG e p)
getTable = BraiderT $ gets (\(BraidState table _) -> table)

insertNode :: (Ord p, Monad m) => BAC e -> [Edge e p] -> BraiderT e p m p
insertNode node children = BraiderT $ do
  state <- get
  let BraidState table (p : counter') = state
  let table' = insert p (node, children) table
  put $ BraidState table' counter'
  return p

data Edge e p = Edge e p

-- | Make a knot in the Braider.
knot :: (Enum p, Ord p, Monad m) => [Edge e p] -> BraiderT e p m p
knot children = do
  table <- getTable

  let nums =
        children
        |> fmap ((\(Edge _ p) -> p) .> (table !) .> fst .> symbols .> maximum .> (+ 1))
        |> scanl (+) 1
  let node =
        children
        |> fmap (\(Edge e p) -> (e, fst (table ! p)))
        |> zip nums
        |> fmap (\(num, (e, subnode)) -> Arrow {
            dict = subnode |> symbols |> fmap (\a -> (a, num + a)) |> Map.fromList,
            value = e,
            target = subnode
          }
        )
        |> BAC

  insertNode node children

newtype Path = Path [Int]

expandMergingSymbols :: [[Dict]] -> [[Symbol]]
expandMergingSymbols =
  fmap (fmap Map.toList)
  .> zip [0 :: Integer ..]
  .> concatMap sequence
  .> concatMap sequence
  .> fmap (\(a, (b, c)) -> ((a, b), c))
  .> bipartiteEqclass
  .> fmap snd
  .> filter (length .> (> 1))
  .> fmap sort
  .> sort

-- | Merge symbols in the Braider.
infixl 2 //
(//) :: (Enum p, Ord p, Monad m) => BraiderT e p m p -> [Path] -> BraiderT e p m p
braiding // eqclass_paths = do
  p <- braiding
  table <- getTable
  let (node, children) = table ! p
  let eqclass = eqclass_paths |> fmap (\(Path list) -> list)

  let pathToPointer = foldlM (\p index -> p |> (table !) |> snd |> fmap (\(Edge _ p) -> p) |> (!? index)) p

  ptrs <- eqclass |> traverse (pathToPointer .> maybe empty return)
  guard $ ptrs |> nub |> length |> (<= 1)
  guard $ ptrs /= [p]

  let root' node = symbols node |> fmap (\a -> (a, a)) |> Map.fromList |> (, node)
  let extend' (d, node) = node |> edges |> fmap (\edge -> (d `cat` dict edge, target edge))
  let pathToDict = foldl (\arr' index -> arr' |> extend' |> (!! index)) (root' node) |> fmap fst

  let eqclass' =
        eqclass
        |> fmap pathToDict
        |> return
        |> expandMergingSymbols

  let mergeSymbol sym = eqclass' |> find (elem sym) |> fmap head |> fromMaybe sym
  let merged_edges = do
        arr <- edges node
        let merged_dict = dict arr |> fmap mergeSymbol
        return arr {dict = merged_dict}
  let merged_node = BAC merged_edges

  insertNode merged_node children

type Pointer = Integer

-- | Make a BAC by a monad-typed builder.
braidM :: Monad m => (forall p. (Enum p, Ord p) => BraiderT e p m p) -> m (Maybe (BAC e))
braidM braiding = runMaybeT $ do
  let init = BraidState mempty [toEnum 0 :: Pointer ..]
  (p, final) <- runStateT (runBraiderT braiding) init
  let BraidState table _ = final
  let (res, _) = table ! p
  return res

braid :: (forall p. (Enum p, Ord p) => BraiderT e p Identity p) -> Maybe (BAC e)
braid braiding = runIdentity (braidM braiding)
