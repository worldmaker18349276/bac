module Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet, canonicalizeEqlistSetBruteForce, verify) where

import Data.List.Extra (groupSortOn, allSame)
import Data.List (nub, elemIndex, sort, delete)
import Data.Maybe (fromJust, fromMaybe)
import Control.Arrow ((&&&))


type EqSet a = [a]

-- | Canonicalize a set of eqlists by relabeling.
canonicalizeEqlistSetBruteForce :: Eq a => EqSet [a] -> [[a]]
canonicalizeEqlistSetBruteForce eqlistset =
  head $ groupSortOn (`key` eqlistset) $ perms $ nub $ concat eqlistset
  where
  key :: Eq a => [a] -> EqSet [a] -> [[Int]]
  key order = sort . fmap (fmap (fromJust . (`elemIndex` order)))
  perms :: [a] -> [[a]]
  perms = foldr (concatMap . inserts) [[]]
  inserts :: a -> [a] -> [[a]]
  inserts a [] = [[a]]
  inserts a (b:c) = (a:b:c) : ((b:) <$> inserts a c)

-- | Verify the solution.
--
--   Examples:
--
--   >>> eqlistset = [[1,2], [2,3], [3,4], [4,1]] :: EqSet [Int]
--   >>> verify eqlistset (canonicalizeEqlistSetBruteForce eqlistset)
--   True
--
--   >>> eqlistset' = [[1,2,3], [3,2,1], [1,4,3], [3,4,1]] :: EqSet [Int]
--   >>> verify eqlistset' (canonicalizeEqlistSetBruteForce eqlistset')
--   True
verify :: Eq a => EqSet [a] -> [[a]] -> Bool
verify eqlistset orders = allSame $ fmap (`key` eqlistset) orders
  where
  key :: Eq a => [a] -> EqSet [a] -> [[Int]]
  key order = sort . fmap (sort . fmap (fromJust . (`elemIndex` order)))

-- | Canonicalize a set of eqlists by relabeling.
--
--   Examples:
--
--   >>> canonicalizeEqlistSet ([[1,2], [2,3], [3,4], [4,1]] :: EqSet [Int])
--   [[1,2,4,3],[2,3,1,4],[3,4,2,1],[4,1,3,2]]
--
--   >>> canonicalizeEqlistSet ([[1,2,3], [3,2,1], [1,4,3], [3,4,1]] :: EqSet [Int])
--   [[1,2,3,4],[3,2,1,4],[1,4,3,2],[3,4,1,2]]
canonicalizeEqlistSet :: Eq a => EqSet [a] -> [[a]]
canonicalizeEqlistSet = canonicalizeGradedEqlistSet (const ())

-- TODO: further refine grades and groups by adjacent vertices

-- | Canonicalize a set of graded eqlists by relabeling.
canonicalizeGradedEqlistSet :: (Eq a, Ord g) => (a -> g) -> EqSet [a] -> [[a]]
canonicalizeGradedEqlistSet grade =
  fmap fst . go . set . fmap (fmap nub) . groupSortOn (fmap grade &&& label)
  where
  label :: Eq a => [a] -> [Int]
  label a = fromJust . (`elemIndex` nub a) <$> a

  set :: Eq a => [[[a]]] -> [([a], [[[a]]])]
  set groups = [([], groups)]

  go :: Eq a => [([a], [[[a]]])] -> [([a], [[[a]]])]
  go states =
    if null (snd (head states))
    then states
    else go $ fmap snd $ head $ groupSortOn fst $ concatMap next states

  next :: Eq a => ([a], [[[a]]]) -> [([(Int, Int)], ([a], [[[a]]]))]
  next (order, []) = [([], (order, []))]
  next (order, []:rest) = next (order, rest)
  next (order, group:rest) = do
    eqlist <- head $ groupSortOn (keyBy order) group
    let order' = order ++ nub (filter (`notElem` order) eqlist)
    let group' = delete eqlist group
    let key = keyBy order' eqlist
    return (key, (order', group':rest))

  keyBy :: Eq a => [a] -> [a] -> [(Int, Int)]
  keyBy order =
    sort . (`zip` [0..]) . fmap (fromMaybe (length order) . (`elemIndex` order))
