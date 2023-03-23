{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

module Utils.DisjointSet (bipartiteEqclass, bipartiteEqclassOn) where

import Data.Foldable (foldr')
import Data.List (nub)
import Data.List.Extra (nubOn)

bipartiteEqclass :: (Eq a, Eq b) => [(a, b)] -> [([a], [b])]
bipartiteEqclass = foldr' addLink []

addLink :: (Eq a, Eq b) => (a, b) -> [([a], [b])] -> [([a], [b])]
addLink (a, b) links = ablink : filter (not . intersect) links
  where
  intersect (as, bs) = a `elem` as || b `elem` bs
  (as, bs) = unzip (filter intersect links)
  ablink = (nub $ a : concat as, nub $ b : concat bs)

bipartiteEqclassOn :: (Eq a, Eq b) => (x -> a) -> (y -> b) -> [(x, y)] -> [([x], [y])]
bipartiteEqclassOn k1 k2 = foldr' (addLinkOn k1 k2) []

addLinkOn :: (Eq a, Eq b) => (x -> a) -> (y -> b) -> (x, y) -> [([x], [y])] -> [([x], [y])]
addLinkOn k1 k2 (x, y) links = ablink : filter (not . intersect) links
  where
  intersect (xs, ys) = k1 x `elem` fmap k1 xs || k2 y `elem` fmap k2 ys
  (xs, ys) = unzip (filter intersect links)
  ablink = (nubOn k1 $ x : concat xs, nubOn k2 $ y : concat ys)

