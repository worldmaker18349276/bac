{-# LANGUAGE BlockArguments #-}
module Utils where

infixl 1 |>
(|>) :: a -> (a -> b) -> b
a |> b = b a

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
a .> b = b . a

fromLeft :: Either a b -> a
fromLeft (Left a) = a

fromRight :: Either a b -> b
fromRight (Right b) = b


range     :: Int -> Int -> [a] -> [a]
range from to = take to .> drop from

rangeFrom :: Int        -> [a] -> [a]
rangeFrom = drop

rangeTo   ::        Int -> [a] -> [a]
rangeTo = take

splice :: Int -> Int -> [a] -> [a] -> [a]
splice from to elems list = rangeTo from list ++ elems ++ rangeFrom to list

foldl1M :: Monad m => (a -> a -> m a) -> [a] -> m a
foldl1M f = fmap return .> foldl1 \a b -> do { a <- a; b <- b; f a b }

allSameBy :: (a -> a -> Bool) -> [a] -> Bool
allSameBy _ [] = True
allSameBy f (a:t) = all (f a) t

allComb :: (a -> a -> Bool) -> [a] -> Bool
allComb _ [] = True
allComb f (h:t) = all (f h) t && allComb f t

untilM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a
untilM cond next val
  | cond val = return val
  | otherwise = do
    val' <- next val
    untilM cond next val'

untilJustM :: Monad m => (a -> Maybe b) -> (a -> m a) -> a -> m b
untilJustM cond next val = case cond val of
  Just val -> return val
  Nothing -> do
    val' <- next val
    untilJustM cond next val'
