{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module DAG (DAG, index, value, children, BuilderT, Builder, Pointer (toInt), getTable,
  buildM, build, node) where

import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.State (StateT, get, gets, put, runStateT)
import Control.Monad.Trans (MonadTrans)
import Data.Map (Map, insert, (!))

data DAG e n = DAG (Map Int (n, [(e, Int)])) Int deriving (Eq, Ord, Show)

index :: DAG e n -> Int
index (DAG _ p) = p

value :: DAG e n -> n
value (DAG table p) = fst $ (fmap $ fmap $ fmap $ DAG table) (table ! p)

children :: DAG e n -> [(e, DAG e n)]
children (DAG table p) = snd $ (fmap $ fmap $ fmap $ DAG table) (table ! p)

data BuildState e n p = BuildState (Map p (n, [(e, p)])) [p]

newtype BuilderT e n p m v = BuilderT {runBuilderT :: StateT (BuildState e n p) m v}
  deriving (Functor, Applicative, Monad, MonadTrans)

type Builder e n p v = BuilderT e n p Identity v

getTable :: Monad m => BuilderT e n p m (Map p (n, [(e, p)]))
getTable = BuilderT $ gets (\(BuildState table _) -> table)

class Ord p => Pointer p where
  toInt :: p -> Int

instance Pointer Int where
  toInt = id

buildM :: Monad m => (forall p. Pointer p => BuilderT e n p m p) -> m (DAG e n)
buildM building = do
  let init = BuildState mempty [0 ..]
  (p, final) <- runStateT (runBuilderT building) init
  let BuildState table _ = final
  return $ DAG table p

{- | Make a DAG by a monad-typed builder.

Examples:

>>> :{
build $ do
  a <- node "a" []
  b <- node "b" [("1", a)]
  c <- node "c" [("2", a), ("3", b)]
  node "d" [("4", b), ("5", c)]
:}
DAG (fromList [(0,("a",[])),(1,("b",[("1",0)])),(2,("c",[("2",0),("3",1)])),(3,("d",[("4",1),("5",2)]))]) 3

It is equivalent to:

>>> :{
let
  a = (0 :: Int, ("a", []))
  b = (1 :: Int, ("b", [("1", fst a)]))
  c = (2 :: Int, ("c", [("2", fst a), ("3", fst b)]))
  d = (3 :: Int, ("d", [("4", fst b), ("5", fst c)]))
in
  DAG (Data.Map.fromList [a, b, c, d]) (fst d)
:}
DAG (fromList [(0,("a",[])),(1,("b",[("1",0)])),(2,("c",[("2",0),("3",1)])),(3,("d",[("4",1),("5",2)]))]) 3

-}
build :: (forall p. Pointer p => Builder e n p p) -> DAG e n
build building = runIdentity (buildM building)

node :: (Pointer p, Monad m) => n -> [(e, p)] -> BuilderT e n p m p
node value children = BuilderT $ do
  state <- get
  let BuildState table (p : counter') = state
  let table' = insert p (value, children) table
  put $ BuildState table' counter'
  return p
