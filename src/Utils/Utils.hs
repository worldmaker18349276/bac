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

toMaybe :: Bool -> a -> Maybe a
toMaybe b a = if b then Just a else Nothing

ensure :: Alternative f => (a -> Bool) -> a -> f a
ensure f a = if f a then pure a else empty

allSameBy :: (a -> a -> Bool) -> [a] -> Bool
allSameBy f = nubBy f .> length .> (<= 1)

label :: (Eq a, Enum e) => e -> [a] -> [e]
label e a = a |> fmap (`lookup` labels) |> fmap fromJust
  where
  labels = nub a `zip` [e..]
