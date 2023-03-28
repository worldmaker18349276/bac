module Utils.EqlistSet (canonicalizeEqlistSet, canonicalizeGradedEqlistSet, canonicalizeEqlistSetBruteForce) where

import Data.List.Extra (groupSortOn)
import Data.List (nub, elemIndex, sort, delete)
import Data.Maybe (fromJust, fromMaybe)
import Control.Arrow ((&&&))


type EqSet a = [a]

-- canonicalize a set of eqlists by relabeling.
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


canonicalizeEqlistSet :: Eq a => EqSet [a] -> [[a]]
canonicalizeEqlistSet = canonicalizeGradedEqlistSet (const ())

-- TODO: further refine grades and groups by adjacent vertices
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
