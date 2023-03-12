module Utils.Memoize (memoizeWithKey, unsafeMemoizeWithKey) where

-- ref: https://stackoverflow.com/a/2238707

import Control.Monad.ST (ST, stToIO)
import Data.Map as Map (empty, insert, lookup)
import Data.STRef (newSTRef, readSTRef, modifySTRef)
import System.IO.Unsafe (unsafePerformIO)

memoizeWithKey :: Ord k => (a -> k) -> (a -> ST s b) -> ST s (a -> ST s b)
memoizeWithKey key f = do
  ref <- newSTRef Map.empty
  return $ \a -> do
    let k = key a
    cache <- readSTRef ref
    case Map.lookup k cache of
      Just b -> return b
      Nothing -> do
        b <- f a
        modifySTRef ref (Map.insert k b)
        return b

unsafeMemoizeWithKey :: Ord k => (a -> k) -> (a -> b) -> a -> b
unsafeMemoizeWithKey key f = unsafePerformIO . stToIO $ do
  ref <- newSTRef Map.empty
  return $ \a -> unsafePerformIO . stToIO $ do
    let k = key a
    cache <- readSTRef ref
    case Map.lookup k cache of
      Just b -> return b
      Nothing -> do
        let b = f a
        modifySTRef ref (Map.insert k b)
        return b
