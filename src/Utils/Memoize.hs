{-# LANGUAGE RankNTypes #-}
module Utils.Memoize (memoizeWithKey) where

import Control.Monad.ST (ST, runST, fixST)
import Data.Map as Map (empty, insert, lookup)
import Data.STRef (newSTRef, readSTRef, modifySTRef)

memoizeWithKey :: Ord k => (a -> k) -> (forall s. (a -> ST s b) -> (a -> ST s b)) -> (a -> b)
memoizeWithKey key f a' = runST $ do
  f' <- fixST $ memo . f
  f' a'
  where
  memo self = do
    ref <- newSTRef Map.empty
    return $ \a -> do
      let k = key a
      cache <- readSTRef ref
      case Map.lookup k cache of
        Just b -> return b
        Nothing -> do
          b <- self a
          modifySTRef ref (Map.insert k b)
          return b
