{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Utils.EqlistSet (
  EqlistSet,
  eqlistKey,
  canonicalizeEqlistSet,
  gradedEqlistKey,
  canonicalizeGradedEqlistSet,
  canonicalizeEqlistSetWithKey,
) where

import Data.List.Extra (groupSortOn)
import Data.List (nub, elemIndex, sort, delete, sortOn)
import Data.Maybe (fromJust, fromMaybe)
import Control.Arrow ((&&&), Arrow (second))


type EqlistSet a = [[a]]

-- | Canonicalize an eqlist set with a given key.  It returns all possible sorted eqlist
--   set which minimize the value of @fmap (key order)@ for a unique order of `a`.
--
--   Examples:
--
--   >>> let key order = fmap (`elemIndex` order)
--   >>> sort $ canonicalizeEqlistSetWithKey key ([[1,2], [2,3], [3,4], [4,1]] :: EqlistSet Int)
--   [[[1,2],[2,3],[3,4],[4,1]],[[2,3],[3,4],[4,1],[1,2]],[[3,4],[4,1],[1,2],[2,3]],[[4,1],[1,2],[2,3],[3,4]]]
--
--   >>> sort $ canonicalizeEqlistSetWithKey key ([[1,2,3], [3,2,1], [1,4,3], [3,4,1]] :: EqlistSet Int)
--   [[[1,2,3],[1,4,3],[3,2,1],[3,4,1]],[[1,4,3],[1,2,3],[3,4,1],[3,2,1]],[[3,2,1],[3,4,1],[1,2,3],[1,4,3]],[[3,4,1],[3,2,1],[1,4,3],[1,2,3]]]
canonicalizeEqlistSetWithKey :: (Eq a, Ord k) => ([a] -> [a] -> k) -> EqlistSet a -> [EqlistSet a]
canonicalizeEqlistSetWithKey key eqlistset =
  fmap (\order -> sortOn (key order) eqlistset)
  $ head $ groupSortOn (`eqlistSetKey` eqlistset)
  $ perms $ nub $ concat eqlistset
  where
  eqlistSetKey order = sort . fmap (key order)
  perms :: [a] -> [[a]]
  perms = foldr (concatMap . inserts) [[]]
  inserts :: a -> [a] -> [[a]]
  inserts a [] = [[a]]
  inserts a (b:c) = (a:b:c) : ((b:) <$> inserts a c)

nubWithIndices :: Eq a => [a] -> ([Int], [a])
nubWithIndices a = (fromJust . (`elemIndex` a') <$> a, a')
  where
  a' = nub a

nublistKey :: Eq a => [a] -> [a] -> [(Int, Int)]
nublistKey order = sort . (`zip` [0..]) . fmap (fromJust . (`elemIndex` order))

eqlistKey :: Eq a => [a] -> [a] -> (Int, ([Int], [(Int, Int)]))
eqlistKey order = length &&& second (nublistKey order) . nubWithIndices

-- | Canonicalize an eqlist set.  It returns all possible sorted indices for the eqlist
--   set.  It is equivalent to @canonicalizeEqlistSetWithKey eqlistKey@ up to order.
--
--   Examples:
--
--   >>> sort $ canonicalizeEqlistSet ([[1,2], [2,3], [3,4], [4,1]] :: EqlistSet Int)
--   [[[1,2],[4,1],[2,3],[3,4]],[[2,3],[1,2],[3,4],[4,1]],[[3,4],[2,3],[4,1],[1,2]],[[4,1],[3,4],[1,2],[2,3]]]
--
--   >>> sort $ canonicalizeEqlistSet ([[1,2,3], [3,2,1], [1,4,3], [3,4,1]] :: EqlistSet Int)
--   [[[1,2,3],[1,4,3],[3,2,1],[3,4,1]],[[1,4,3],[1,2,3],[3,4,1],[3,2,1]],[[3,2,1],[3,4,1],[1,2,3],[1,4,3]],[[3,4,1],[3,2,1],[1,4,3],[1,2,3]]]
canonicalizeEqlistSet :: Eq a => EqlistSet a -> [EqlistSet a]
canonicalizeEqlistSet = canonicalizeGradedEqlistSet (const ())

gradedEqlistKey :: (Eq a, Ord g) => (a -> g) -> [a] -> [a] -> ([g], ([Int], [(Int, Int)]))
gradedEqlistKey grade order = fmap grade &&& second (nublistKey order) . nubWithIndices

-- TODO: further refine grades and groups by adjacent vertices

-- | Canonicalize a graded eqlist set.  It returns all possible sorted indices for the
--   graded eqlist set.  It is equivalent to @canonicalizeEqlistSetWithKey
--   (gradedEqlistKey grade)@ up to order.
canonicalizeGradedEqlistSet :: (Eq a, Ord g) => (a -> g) -> EqlistSet a -> [EqlistSet a]
canonicalizeGradedEqlistSet grade eqlistset =
  fmap (\(order, _) -> sortOn (gradedEqlistKey grade order) eqlistset)
  -- search possibility layer by layer
  $ go $ set
  -- extract out remaining parts
  $ fmap (fmap (snd . snd))
  -- presort eqlist
  $ groupSortOn (second fst)
  -- transform eqlist
  $ fmap (fmap grade &&& nubWithIndices) eqlistset
  where
  set :: Eq a => [[[a]]] -> [([a], [[[a]]])]
  set groups = [([], groups)]

  go :: Eq a => [([a], [[[a]]])] -> [([a], [[[a]]])]
  go states =
    if null $ snd $ head states
    then states
    else go $ fmap snd $ head $ groupSortOn fst $ concatMap next states

  next :: Eq a => ([a], [[[a]]]) -> [([(Int, Int)], ([a], [[[a]]]))]
  next (order, []) = [([], (order, []))]
  next (order, []:rest) = next (order, rest)
  next (order, group:rest) = do
    eqlist <- head $ groupSortOn (partialNublistKey order) group
    let order' = order ++ nub (filter (`notElem` order) eqlist)
    let group' = delete eqlist group
    let key = partialNublistKey order' eqlist
    return (key, (order', group':rest))

  partialNublistKey :: Eq a => [a] -> [a] -> [(Int, Int)]
  partialNublistKey order =
    sort . (`zip` [0..]) . fmap (fromMaybe (length order) . (`elemIndex` order))
