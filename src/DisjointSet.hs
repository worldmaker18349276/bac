module DisjointSet (bipartiteEqclass) where

import Data.Foldable (foldr')
import Data.List (nub)

bipartiteEqclass :: (Ord a, Ord b) => [(a, b)] -> [([a], [b])]
bipartiteEqclass = foldr' addLink []

addLink :: (Ord a, Ord b) => (a, b) -> [([a], [b])] -> [([a], [b])]
addLink (a, b) links = ablink : filter (not . intersect) links
  where
  intersect (as, bs) = a `elem` as || b `elem` bs
  (as, bs) = unzip (filter intersect links)
  ablink = (nub $ a : concat as, nub $ b : concat bs)
