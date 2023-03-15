module Utils.Utils where

import Data.List (groupBy, nub, nubBy)
import Data.Maybe (fromJust)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

both :: (a -> b) -> (a, a) -> (b, b)
both f (a, a') = (f a, f a')

nubOn :: Eq b => (a -> b) -> [a] -> [a]
nubOn f = nubBy (\a a' -> f a == f a')

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy (\a a' -> f a == f a')

toMaybe :: Bool -> a -> Maybe a
toMaybe b a = if b then Just a else Nothing

filterMaybe :: (a -> Bool) -> a -> Maybe a
filterMaybe f a = if f a then Just a else Nothing

allSame :: Eq a => [a] -> Bool
allSame = nub .> length .> (<= 1)

allSameBy :: (a -> a -> Bool) -> [a] -> Bool
allSameBy f = nubBy f .> length .> (<= 1)

distinct :: Eq a => [a] -> Bool
distinct a = nub a == a

label :: (Eq a, Enum e) => e -> [a] -> [e]
label e a = a |> fmap (`lookup` labels) |> fmap fromJust
  where
  labels = nub a `zip` [e..]
