module Utils.Utils ((|>), (.>), guarded) where

import Control.Applicative (Alternative (empty))

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

guarded :: Alternative f => (a -> Bool) -> a -> f a
guarded f a = if f a then pure a else empty
