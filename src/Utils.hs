module Utils where

import Data.List (groupBy, nubBy)

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

