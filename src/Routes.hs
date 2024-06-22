{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Routes (
  Compass,
  Route,
  PrefixOrdering (..),
  toOrdering,
  comparePrefix,
  fromBAC,
  fromString,
  getString,
  searchString,
  equal,
  trimr,
  triml,
  root,
  source,
  target,
  extendr,
  extendl,
  dividel,
  divider,
  swing,
  addEdge,
  removeEdge,
  isNondecomposable,
  removeRoute,
  removeTarget,
) where

import Control.Monad (guard)
import Data.Foldable (find)
import Data.List (uncons)
import Data.List.Extra (firstJust, snoc, unsnoc)
import Data.Maybe (fromJust, isJust, isNothing, mapMaybe)

import BAC.Base (BAC, Arrow)
import qualified BAC.Base as BAC
import qualified BAC.Fundamental.Split as Split
import Utils.Utils ((|>), (.>))
import qualified BAC.Fundamental.Restructure as Restructure
import qualified BAC.Fundamental.Remove as Remove


data PrefixOrdering = LessBy String | Equal | GreaterBy String deriving (Eq, Ord, Show)

toOrdering :: PrefixOrdering -> Ordering
toOrdering (LessBy _) = LT
toOrdering (GreaterBy _) = GT
toOrdering Equal = EQ

comparePrefix :: String -> String -> Maybe PrefixOrdering
comparePrefix [] [] = Just Equal
comparePrefix surf@(_:_) [] = Just (GreaterBy surf)
comparePrefix [] surf@(_:_) = Just (LessBy surf)
comparePrefix (h:t) (h':t') = if h == h' then comparePrefix t t' else Nothing

strip :: String -> String -> Maybe String
strip str [] = Just str
strip [] _ = Nothing
strip (h:t) (h':t') = if h == h' then strip t t' else Nothing

newtype Compass = Compass (BAC String)

data Route = Route (Arrow String) [Arrow String]
allComb :: (a -> a -> Bool) -> [a] -> Bool
allComb _ [] = True
allComb f (h:t) = all (f h) t && allComb f t

fromBAC :: BAC String -> Maybe Compass
fromBAC node = do
  guard $
    BAC.arrows node
    |> concatMap (BAC.target .> BAC.edges)
    |> fmap BAC.value
    |> allComb (\a b -> isNothing (a `comparePrefix` b))
  return $ Compass node

findSource :: BAC String -> String -> Maybe (Arrow String)
findSource node str =
  BAC.arrows node
  |> find (
    BAC.target
    .> BAC.edges
    .> fmap BAC.value
    .> fmap (strip str)
    .> any isJust
  )

searchString :: Compass -> String -> [PrefixOrdering]
searchString (Compass node) str =
  BAC.arrows node
  |> concatMap (
    BAC.target
    .> BAC.edges
  )
  |> mapMaybe (BAC.value .> comparePrefix str)

follow :: BAC String -> String -> Maybe [Arrow String]
follow = go []
  where
  go res _node [] = Just res
  go res node str = node |> BAC.edges |> firstJust \edge -> do
    surf <- strip str (BAC.value edge)
    go (res `snoc` edge) (BAC.target edge) surf

fromString :: Compass -> String -> Maybe Route
fromString (Compass node) str = do
  arr <- findSource node str
  chain <- follow (BAC.target arr) str
  return $ Route arr chain

fromArrow :: (Arrow String, Arrow String) -> Route
fromArrow (arr1, arr2) = Route arr1 (fromJust $ BAC.chain (BAC.target arr1) (BAC.symbol arr2))

getString :: Route -> String
getString (Route _ chain) = concatMap BAC.value chain

getArrow :: Route -> (Arrow String, Arrow String)
getArrow (Route arr chain) = case chain of
  [] -> (arr, BAC.root (BAC.target arr))
  h : t -> (arr, foldl BAC.join h t)

root :: Compass -> Route
root (Compass node) = Route (BAC.root node) []

equal :: Route -> Route -> Bool
equal route1 route2 = BAC.symbol2 (getArrow route1) == BAC.symbol2 (getArrow route2)

trimr :: Route -> Maybe Route
trimr (Route arr chain) = unsnoc chain |> fmap fst |> fmap (Route arr)

triml :: Route -> Maybe Route
triml (Route arr chain) = uncons chain |> fmap (\(h, t) -> Route (arr `BAC.join` h) t)

source :: Route -> Route
source (Route arr _) = Route arr []

target :: Route -> Route
target (Route arr chain) = Route (foldl BAC.join arr chain) []

extendr :: Compass -> Route -> [Route]
extendr _ (Route arr chain) =
  (arr : chain) |> last |> BAC.target |> BAC.edges |> fmap \edge -> Route arr (chain `snoc` edge)

extendl :: Compass -> Route -> [Route]
extendl (Compass node) (Route arr chain) =
  BAC.suffix node (BAC.symbol arr) |> fmap \(arr', edge) -> Route arr' (edge : chain)

dividel :: Route -> Route -> Maybe [Route]
dividel route1 route2 = do
  let arr_arr1 = getArrow route1
  let arr_arr2 = getArrow route2
  guard $ BAC.symbol (fst arr_arr1) == BAC.symbol (fst arr_arr2)
  let arrs = snd arr_arr1 `BAC.divide` snd arr_arr2
  let arr3 = uncurry BAC.join arr_arr1
  return $ arrs |> fmap (BAC.symbol .> BAC.chain (BAC.target arr3) .> fromJust .> Route arr3)

divider :: Route -> Route -> Maybe [Route]
divider route1 route2 = do
  let arr_arr1 = getArrow route1
  let arr_arr2 = getArrow route2
  guard $ BAC.symbol (uncurry BAC.join arr_arr1) == BAC.symbol (uncurry BAC.join arr_arr2)
  let syms = BAC.inv (BAC.dict (fst arr_arr2)) (BAC.symbol (fst arr_arr1))
  return $ syms |> fmap (BAC.chain (BAC.target (fst arr_arr1)) .> fromJust .> Route (fst arr_arr2))

swing :: Route -> (Int, Int) -> Maybe [Route]
swing (Route arr chain) (start, end) = do
  guard $ 0 < start && start < length chain
  guard $ 1 < end && end <= length chain
  guard $ start < end
  let subchain = chain |> drop start |> take (end - start)
  let subarr0 = BAC.root (BAC.target ((arr : chain) !! start))
  let subarr = foldl BAC.join subarr0 subchain
  let subchains =
        Split.partitionPrefix (BAC.target subarr0) (BAC.symbol subarr)
        |> fmap head
        |> fmap (\(sym1, sym2) -> (fromJust $ BAC.arrow (BAC.target subarr0) sym1, sym2))
        |> fmap (\(arr1, sym2) -> arr1 : fromJust (BAC.chain (BAC.target arr1) sym2))
        |> (++ (BAC.edges (BAC.target subarr0) |> filter (BAC.symbol .> (== BAC.symbol subarr)) |> fmap (: [])))
  return $ subchains |> fmap \subchain -> Route arr (take start chain ++ subchain ++ drop end chain)

addEdge :: Compass -> Route -> String -> Maybe Compass
addEdge com@(Compass node) route str = do
  guard $ null $ searchString com (getString route)
  node' <- Restructure.addEdge (BAC.symbol2 (getArrow route)) str node
  return $ Compass node'

removeEdge :: Compass -> Route -> Maybe Compass
removeEdge (Compass node) route@(Route _ chain) = do
  guard $ length chain == 1
  let arr_arr = getArrow route
  let value = BAC.value (snd arr_arr)
  let edges = BAC.target (fst arr_arr) |> BAC.edges |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
  guard $ edges |> any (BAC.value .> (== value))
  node' <- Restructure.removeEdge (BAC.symbol2 arr_arr) value node
  return $ Compass node'

isNondecomposable :: Route -> Bool
isNondecomposable (Route arr chain) =
  length chain == 1 && BAC.nondecomposable (BAC.target arr) (BAC.symbol (head chain))

removeRoute :: Compass -> Route -> Maybe Compass
removeRoute (Compass node) route = do
  let arr_arr = getArrow route
  guard $ fst arr_arr |> BAC.symbol |> (/= BAC.base)
  node' <- Remove.removeNDSymbol (BAC.symbol2 arr_arr) node
  return $ Compass node'

removeTarget :: Compass -> Route -> Maybe Compass
removeTarget (Compass node) route = do
  let arr = getArrow route |> uncurry BAC.join
  node' <- Remove.removeNode (BAC.symbol arr) node
  return $ Compass node'
