module Utils.Utils ((|>), (.>), orEmpty, guarded, label, mergeNubOn, foldlMUncurry) where

import Data.List (nub)
import Data.Maybe (fromJust)
import Control.Applicative (Alternative (empty))
import Data.Foldable (foldlM)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

orEmpty :: Alternative f => Bool -> a -> f a
orEmpty b a = if b then pure a else empty

guarded :: Alternative f => (a -> Bool) -> a -> f a
guarded f a = if f a then pure a else empty

label :: (Eq a, Enum e) => e -> [a] -> [e]
label e a = a |> fmap (`lookup` labels) |> fmap fromJust
  where
  labels = nub a `zip` [e..]

mergeNubOn :: Eq b => (a -> b) -> [[a]] -> [a]
mergeNubOn f = foldr mergeNub []
  where
  mergeNub list = foldr (insertNub (fmap f list)) list
  insertNub keys a = if f a `elem` keys then id else (a :)

foldlMUncurry :: (Foldable t, Monad m) => ((b, a) -> m b) -> (b, t a) -> m b
foldlMUncurry = uncurry . foldlM . curry
