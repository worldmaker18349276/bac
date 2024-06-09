module Utils.Utils ((|>), (.>), guarded, asserted, zipIf) where

import Control.Applicative (Alternative (empty))
import GHC.Stack (HasCallStack)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

guarded :: Alternative f => (a -> Bool) -> a -> f a
guarded f a = if f a then pure a else empty

asserted :: HasCallStack => (a -> Bool) -> a -> a
asserted f a = if f a then a else error "assertion fail"

zipIf :: (b -> Bool) -> [a] -> [b] -> [(Maybe a, b)]
zipIf _ _ [] = []
zipIf f [] (h:t) = (Nothing, h) : zipIf f [] t
zipIf f (a:b) (h:t) = if f h then (Just a, h) : zipIf f b t else (Nothing, h) : zipIf f (a:b) t
