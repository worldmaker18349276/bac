module Utils.Utils ((|>), (.>), guarded, foldlMUncurry) where

import Control.Applicative (Alternative (empty))
import Data.Foldable (foldlM)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

guarded :: Alternative f => (a -> Bool) -> a -> f a
guarded f a = if f a then pure a else empty

foldlMUncurry :: (Foldable t, Monad m) => ((b, a) -> m b) -> (b, t a) -> m b
foldlMUncurry = uncurry . foldlM . curry
