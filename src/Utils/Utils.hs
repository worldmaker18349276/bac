module Utils.Utils where

import Data.List (nub, nubBy)
import Data.Maybe (fromJust)
import Control.Applicative (Alternative (empty))

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

both :: (a -> b) -> (a, a) -> (b, b)
both f (a, a') = (f a, f a')

orEmpty :: Alternative f => Bool -> a -> f a
orEmpty b a = if b then pure a else empty

guarded :: Alternative f => (a -> Bool) -> a -> f a
guarded f a = if f a then pure a else empty

allSameBy :: (a -> a -> Bool) -> [a] -> Bool
allSameBy f = nubBy f .> length .> (<= 1)

label :: (Eq a, Enum e) => e -> [a] -> [e]
label e a = a |> fmap (`lookup` labels) |> fmap fromJust
  where
  labels = nub a `zip` [e..]
