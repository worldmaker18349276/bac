{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Braider (
  BraiderT,
  knot,
  Path (..),
  (//),
  braidM,
  braid,
) where

import Control.Applicative (Alternative (empty))
import Control.Monad (guard)
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.State (MonadState (get, put), StateT (runStateT), gets)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Data.Foldable (find, foldlM)
import Data.List (nub)
import Data.List.Extra ((!?))
import Data.Map.Strict (Map, insert, (!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

import BAC.Base hiding (empty)
import BAC.Fundamental (expandMergingSymbols)
import Utils.Utils ((|>), (.>))

type DAG p = Map p (BAC, [p])
data BraidState p = BraidState (DAG p) [p]

newtype BraiderT p m v = BraiderT {runBraiderT :: StateT (BraidState p) (MaybeT m) v}
  deriving (Functor, Applicative, Alternative, Monad)

getTable :: Monad m => BraiderT p m (DAG p)
getTable = BraiderT $ gets (\(BraidState table _) -> table)

insertNode :: (Ord p, Monad m) => BAC -> [p] -> BraiderT p m p
insertNode node children = BraiderT $ do
  state <- get
  let BraidState table (p : counter') = state
  let table' = insert p (node, children) table
  put $ BraidState table' counter'
  return p

-- | Make a knot in the Braider.
knot :: (Enum p, Ord p, Monad m) => [p] -> BraiderT p m p
knot children = do
  table <- getTable

  let nums =
        children
        |> fmap ((table !) .> fst .> symbols .> maximum .> (+ 1))
        |> scanl (+) 1
  let node =
        children
        |> fmap (table !)
        |> fmap fst
        |> zip nums
        |> fmap (\(num, subnode) -> Arrow {
            dict = subnode |> symbols |> fmap (\a -> (a, num + a)) |> Map.fromList,
            target = subnode
          }
        )
        |> fromEdges

  insertNode node children

newtype Path = Path [Int]

-- | Merge symbols in the Braider.
infixl 2 //
(//) :: (Enum p, Ord p, Monad m) => BraiderT p m p -> [Path] -> BraiderT p m p
braiding // eqclass_paths = do
  p <- braiding
  table <- getTable
  let (node, children) = table ! p
  let eqclass = eqclass_paths |> fmap (\(Path list) -> list)

  let pathToPointer = foldlM (\p index -> p |> (table !) |> snd |> (!? index)) p

  ptrs <- eqclass |> traverse (pathToPointer .> maybe empty return)
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

  insertNode merged_node children

type Pointer = Integer

-- | Make a BAC by a monad-typed builder.
braidM :: Monad m => (forall p. (Enum p, Ord p) => BraiderT p m p) -> m (Maybe BAC)
braidM braiding = runMaybeT $ do
  let init = BraidState mempty [toEnum 0 :: Pointer ..]
  (p, final) <- runStateT (runBraiderT braiding) init
  let BraidState table _ = final
  let (res, _) = table ! p
  return res

braid :: (forall p. (Enum p, Ord p) => BraiderT p Identity p) -> Maybe BAC
braid braiding = runIdentity (braidM braiding)
