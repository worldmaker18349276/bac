{-# LANGUAGE BlockArguments #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use null" #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant id" #-}
{-# LANGUAGE TupleSections #-}

module Prefix (
  PrefixOrdering (..),
  toOrdering,
  comparePrefix,
  PrefixBAC,
  Chain,
  Node,
  fromBAC,
  searchString,
  fromString,
  getStrings,
  getPreString,
  root,
  trimr,
  triml,
  source,
  target,
  id,
  init,
  outgoing,
  incoming,
  concat,
  length,
  split,
  dividel,
  divider,
  (==-),
  (===),
  (==~),
  addEdge,
  removeEdge,
  alterEdge,
  isNondecomposable,
  removeMorphism,
  removeObject,
  Cofraction,
  Fraction,
  ChainRule,
  getPossibleChainRules,
  compatibleChainRule,
  addMorphism,
  addObject,
  interpolateObject,
  prefixes,
  suffixes,
  partitionPrefixesSuffixes,
  unsplittable,
  swing,
  splitMorphism,
  paritionIncoming,
  splitObjectIncoming,
  partitionOutgoing,
  splitObjectOutgoing,
  splitCategory,
  mergeMorphsisms,
  outgoingCanonicalOrders,
  incomingCanonicalOrders,
  findOutgoingZippableObjects,
  findIncomingZippableObjects,
  mergeObjectsIncoming,
  mergeObjectsOutgoing,
  mergeCategories,
) where

import Control.Monad (guard)
import Data.Bifunctor (bimap, first)
import Data.Char (isPrint)
import Data.Foldable (find)
import Data.Foldable.Extra (foldrM)
import Data.List (elemIndex, findIndices, sort, uncons)
import qualified Data.List as List
import Data.List.Extra (allSame, firstJust, notNull, nubSort, snoc, unsnoc)
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Maybe (fromJust, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)
import Prelude hiding (concat, id, init, length)
import qualified Prelude

import BAC.Base (Arrow, BAC, Symbol)
import qualified BAC.Base as BAC
import qualified BAC.Fundamental.Add as Add
import qualified BAC.Fundamental.Merge as Merge
import qualified BAC.Fundamental.Remove as Remove
import qualified BAC.Fundamental.Restructure as Restructure
import qualified BAC.Fundamental.Split as Split
import qualified BAC.Fundamental.Zip as Zip
import Utils.Utils ((.>), (|>))


data PrefixOrdering = LessBy String | Equal | GreaterBy String deriving (Eq, Ord, Show)

toOrdering :: PrefixOrdering -> Ordering
toOrdering (LessBy _) = LT
toOrdering (GreaterBy _) = GT
toOrdering Equal = EQ

comparePrefix :: String -> String -> Maybe PrefixOrdering
comparePrefix [] [] = Just Equal
comparePrefix suff@(_:_) [] = Just (GreaterBy suff)
comparePrefix [] suff@(_:_) = Just (LessBy suff)
comparePrefix (h:t) (h':t') = if h == h' then comparePrefix t t' else Nothing

strip :: String -> String -> Maybe String
strip str [] = Just str
strip [] _ = Nothing
strip (h:t) (h':t') = if h == h' then strip t t' else Nothing

newtype PrefixBAC = PrefixBAC (BAC String)

data Chain = Chain (Arrow String) [Arrow String]

newtype Node = Node (Arrow String)

allComb :: (a -> a -> Bool) -> [a] -> Bool
allComb _ [] = True
allComb f (h:t) = all (f h) t && allComb f t

fromBAC :: BAC String -> Maybe PrefixBAC
fromBAC bac = do
  let values = BAC.arrows bac
        |> concatMap (BAC.target .> BAC.edges)
        |> fmap BAC.value
  guard $ values |> all (all isPrint)
  guard $ values |> any (elem ' ') |> not
  guard $ values |> allComb \a b -> isNothing (a `comparePrefix` b)
  return $ PrefixBAC bac

searchString :: PrefixBAC -> String -> [PrefixOrdering]
searchString (PrefixBAC bac) str =
  BAC.arrows bac
  |> concatMap (BAC.target .> BAC.edges)
  |> mapMaybe (BAC.value .> comparePrefix str)

fromString :: PrefixBAC -> String -> Maybe Chain
fromString (PrefixBAC bac) str = do
  arr0 <- findSource bac str
  chain <- followString (BAC.target arr0) str
  return $ Chain arr0 chain
  where
  findSource :: BAC String -> String -> Maybe (Arrow String)
  findSource bac str =
    BAC.arrows bac
    |> find (
      BAC.target
      .> BAC.edges
      .> fmap BAC.value
      .> fmap (strip str)
      .> any isJust
    )

  followString :: BAC String -> String -> Maybe [Arrow String]
  followString = go []
    where
    go res _node [] = Just res
    go res node str = node |> BAC.edges |> firstJust \edge -> do
      suff <- strip str (BAC.value edge)
      go (res `snoc` edge) (BAC.target edge) suff

fromArrow2 :: (Arrow String, Arrow String) -> Chain
fromArrow2 (arr1, arr2) = Chain arr1 (fromJust $ BAC.chain (BAC.target arr1) (BAC.symbol arr2))

fromSymbol2 :: BAC String -> (Symbol, Symbol) -> Maybe Chain
fromSymbol2 bac (sym1, sym2) = do
  arr <- BAC.arrow bac sym1
  chain <- BAC.chain (BAC.target arr) sym2
  return $ Chain arr chain

getStrings :: Chain -> [String]
getStrings (Chain _ arrs) = fmap BAC.value arrs

getPreString :: Chain -> String
getPreString (Chain arr0 _) = BAC.value arr0

getArrow2 :: Chain -> (Arrow String, Arrow String)
getArrow2 (Chain arr0 arrs) = case arrs of
  [] -> (arr0, BAC.root (BAC.target arr0))
  h : t -> (arr0, foldl BAC.join h t)

root :: PrefixBAC -> Node
root (PrefixBAC bac) = Node (BAC.root bac)

trimr :: Chain -> Maybe Chain
trimr (Chain arr0 arrs) = unsnoc arrs |> fmap fst |> fmap (Chain arr0)

triml :: Chain -> Maybe Chain
triml (Chain arr0 arrs) = uncons arrs |> fmap (\(h, t) -> Chain (arr0 `BAC.join` h) t)

source :: Chain -> Node
source (Chain arr0 _) = Node arr0

target :: Chain -> Node
target (Chain arr0 arrs) = Node (foldl BAC.join arr0 arrs)

id :: Node -> Chain
id (Node arr0) = Chain arr0 []

init :: PrefixBAC -> Node -> Chain
init (PrefixBAC bac) (Node arr0) = fromArrow2 (BAC.root bac, arr0)

outgoing :: PrefixBAC -> Node -> [Chain]
outgoing _ (Node arr0) =
  arr0 |> BAC.target |> BAC.edges |> fmap \edge -> Chain arr0 [edge]

incoming :: PrefixBAC -> Node -> [Chain]
incoming (PrefixBAC bac) (Node arr0) =
  BAC.suffix bac (BAC.symbol arr0) |> fmap \(arr, edge) -> Chain arr [edge]

concat :: Chain -> Chain -> Maybe Chain
concat chain1@(Chain arr0 arrs1) chain2@(Chain _ arrs2) = do
  guard $ target chain1 ==- source chain2
  return $ Chain arr0 (arrs1 ++ arrs2)

length :: Chain -> Int
length (Chain _ arrs) = Prelude.length arrs

split :: Int -> Chain -> Maybe (Chain, Chain)
split index (Chain arr0 arrs) = do
  guard $ 0 <= index && index <= Prelude.length arrs
  let chain1 = Chain arr0 (take index arrs)
  let arr0' = getArrow2 chain1 |> uncurry BAC.join
  let chain2 = Chain arr0' (drop index arrs)
  return (chain1, chain2)

dividel :: Chain -> Chain -> Maybe [Chain]
dividel chain1 chain2 = do
  let arr_arr1 = getArrow2 chain1
  let arr_arr2 = getArrow2 chain2
  guard $ BAC.symbol (fst arr_arr1) == BAC.symbol (fst arr_arr2)
  let arrs = snd arr_arr1 `BAC.divide` snd arr_arr2
  let arr3 = uncurry BAC.join arr_arr1
  return $ arrs |> fmap (BAC.symbol .> BAC.chain (BAC.target arr3) .> fromJust .> Chain arr3)

divider :: Chain -> Chain -> Maybe [Chain]
divider chain1 chain2 = do
  let arr_arr1 = getArrow2 chain1
  let arr_arr2 = getArrow2 chain2
  guard $ BAC.symbol (uncurry BAC.join arr_arr1) == BAC.symbol (uncurry BAC.join arr_arr2)
  let syms = BAC.inv (BAC.dict (fst arr_arr2)) (BAC.symbol (fst arr_arr1))
  return $ syms |> fmap (BAC.chain (BAC.target (fst arr_arr1)) .> fromJust .> Chain (fst arr_arr2))

(==-) :: Node -> Node -> Bool
(Node arr1) ==- (Node arr2) = BAC.symbol arr1 == BAC.symbol arr2

(===) :: Chain -> Chain -> Bool
chain1@(Chain arr1 _) === chain2@(Chain arr2 _) =
  BAC.symbol arr1 == BAC.symbol arr2 && getStrings chain1 == getStrings chain2

(==~) :: Chain -> Chain -> Bool
chain1 ==~ chain2 = BAC.symbol2 (getArrow2 chain1) == BAC.symbol2 (getArrow2 chain2)

addEdge :: Chain -> String -> PrefixBAC -> Maybe PrefixBAC
addEdge chain str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac (Prelude.concat (getStrings chain))
  bac' <- Restructure.addEdge (BAC.symbol2 (getArrow2 chain)) str bac
  return $ PrefixBAC bac'

removeEdge :: Chain -> PrefixBAC -> Maybe PrefixBAC
removeEdge chain@(Chain _ arrs) (PrefixBAC bac) = do
  guard $ Prelude.length arrs == 1
  let arr_arr = getArrow2 chain
  let value = BAC.value (snd arr_arr)
  let edges = BAC.target (fst arr_arr) |> BAC.edges |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
  guard $ edges |> any (BAC.value .> (== value))
  bac' <- Restructure.removeEdge (BAC.symbol2 arr_arr) value bac
  return $ PrefixBAC bac'

alterEdge :: Chain -> String -> PrefixBAC -> Maybe PrefixBAC
alterEdge chain@(Chain _ arrs) str (PrefixBAC bac) = do
  guard $ Prelude.length arrs == 1
  let arr_arr = getArrow2 chain
  let value = BAC.value (snd arr_arr)
  let edges = BAC.target (fst arr_arr) |> BAC.edges |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
  guard $ edges |> any (BAC.value .> (== value))
  bac' <- Restructure.alterEdges (BAC.symbol2 arr_arr) (fmap \val -> if val == value then str else val) bac
  return $ PrefixBAC bac'

isNondecomposable :: Chain -> Bool
isNondecomposable (Chain arr0 arrs) =
  Prelude.length arrs == 1 && BAC.nondecomposable (BAC.target arr0) (BAC.symbol (head arrs))

modifyOutgoingValues :: Monoid e => Symbol -> (e -> e) -> BAC e -> BAC e
modifyOutgoingValues sym f bac =
  fromJust $ BAC.fromInner $ BAC.root bac |> BAC.modifyUnder sym \(_curr, edge) -> \case
    BAC.AtOuter -> return edge
    BAC.AtBoundary -> return edge {BAC.target = tgt_node'}
    BAC.AtInner res -> return edge {BAC.target = res}
  where
  tgt_node = BAC.target $ fromJust $ BAC.arrow bac sym
  tgt_node' = tgt_node |> BAC.edges |> fmap (\edge -> edge {BAC.value = f (BAC.value edge)}) |> BAC.BAC

modifyIncomingValues :: Monoid e => Symbol -> (e -> e) -> BAC e -> BAC e
modifyIncomingValues sym f bac =
  fromJust $ BAC.fromInner $ BAC.root bac |> BAC.modifyUnder sym \(_curr, edge) -> \case
    BAC.AtOuter -> return edge
    BAC.AtBoundary -> return edge {BAC.value = f (BAC.value edge)}
    BAC.AtInner res -> return edge {BAC.target = res}

removeMorphism :: Chain -> String -> PrefixBAC -> Maybe (PrefixBAC, [String] -> [[String]])
removeMorphism chain str pbac@(PrefixBAC bac) = do
  let arr_arr = getArrow2 chain
  let src_sym = BAC.symbol (fst arr_arr)
  let tgt_sym = BAC.symbol (uncurry BAC.join arr_arr)
  guard $ fst arr_arr |> BAC.symbol |> (/= BAC.base)
  guard $ null $ searchString pbac str

  bac' <- Remove.removeNDSymbol (BAC.symbol2 arr_arr) bac
  let bac'' =
        bac'
        |> modifyOutgoingValues tgt_sym (str ++)
        |> modifyIncomingValues src_sym (++ str)

  let removed =
        BAC.target (fst arr_arr)
        |> BAC.edges
        |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
        |> fmap BAC.value
  let outgoing = BAC.target (snd arr_arr) |> BAC.edges |> fmap BAC.value
  let incoming = BAC.suffix bac (BAC.symbol (fst arr_arr)) |> fmap (snd .> BAC.value)
  let updater tokens =
        case (
          incoming |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          removed |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          outgoing |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, Nothing, Nothing) ->
            [tokens]
          (Nothing, Just _, Nothing) -> -- List.length tokens == 1
            []
          (Just i, Just j, Nothing) -> -- i + 1 == j && j + 1 == List.length tokens
            [take i tokens `snoc` (tokens !! i ++ tokens !! j)]
          (Nothing, Just j, Just k) -> -- j + 1 == k && j == 0
            [(tokens !! j ++ tokens !! k) : drop (k + 1) tokens]
          (Just i, Just j, Just k) -> -- i + 1 == j && j + 1 == k
            [
              take i tokens ++ [tokens !! i ++ tokens !! j, str ++ tokens !! k] ++ drop (k + 1) tokens,
              take i tokens ++ [tokens !! i ++ str, tokens !! j ++ tokens !! k] ++ drop (k + 1) tokens
            ]
          (Just i, Nothing, Nothing) ->
            [take i tokens ++ [tokens !! i ++ str] ++ drop (i + 1) tokens]
          (Nothing, Nothing, Just k) ->
            [take k tokens ++ [str ++ tokens !! k] ++ drop (k + 1) tokens]
          (Just i, Nothing, Just k) -> -- i < k
            [
              take i tokens
              ++ [tokens !! i ++ str]
              ++ drop (i + 1) (take k tokens)
              ++ [str ++ tokens !! k]
              ++ drop (k + 1) tokens
            ]

  return (PrefixBAC bac'', updater)

removeObject :: Node -> PrefixBAC -> Maybe (PrefixBAC, [String] -> [[String]])
removeObject (Node arr) (PrefixBAC bac) = do
  bac' <- Remove.removeNode (BAC.symbol arr) bac

  let outgoing = BAC.target arr |> BAC.edges |> fmap BAC.value
  let incoming = BAC.suffix bac (BAC.symbol arr) |> fmap (snd .> BAC.value)
  let updater tokens =
        case (
          outgoing |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          incoming |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, Nothing) ->
            [tokens]
          (Just i, Just j) -> -- i + 1 == j
            [take i tokens ++ [tokens !! i ++ tokens !! j] ++ drop (j + 1) tokens]
          _ ->
            []

  return (PrefixBAC bac', updater)


type Cofraction = (Chain, Chain)
type Fraction = (Chain, Chain)
type ChainRule = ([Cofraction], [Fraction])

getPossibleChainRules :: PrefixBAC -> Node -> Node -> Maybe ([[Cofraction]], [[Fraction]])
getPossibleChainRules (PrefixBAC bac) (Node src_arr) (Node tgt_arr) = do
  selections <- Add.findValidCofractionsFractions (BAC.symbol src_arr) (BAC.symbol tgt_arr) bac
  return $ selections |> both (fmap (fmap (both (fromSymbol2 bac .> fromJust))))

compatibleChainRule :: PrefixBAC -> ChainRule -> Bool
compatibleChainRule (PrefixBAC bac) rule =
  Add.compatibleFractions bac (snd rule')
  && Add.compatibleCofractions bac (fst rule')
  && uncurry (Add.compatibleCofractionsFractions bac) rule'
  where
  rule' = rule |> both (fmap (both (getArrow2 .> BAC.symbol2)))

addMorphism :: Node -> Node -> ChainRule -> String -> PrefixBAC -> Maybe PrefixBAC
addMorphism (Node src_arr) (Node tgt_arr) rule str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str
  guard $ BAC.symbol src_arr /= BAC.base
  let rule' = rule |> both (fmap (both (getArrow2 .> BAC.symbol2)))
  let sym = BAC.target src_arr |> BAC.symbols |> maximum |> (+ 1)
  bac' <- Add.addNDSymbol (BAC.symbol src_arr) (BAC.symbol tgt_arr) sym str (fst rule') (snd rule') bac
  return $ PrefixBAC bac'

addObject :: Node -> String -> PrefixBAC -> Maybe PrefixBAC
addObject (Node src_arr) str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str
  let sym = BAC.target src_arr |> BAC.symbols |> maximum |> (+ 1)
  bac' <- Add.addLeafNode (BAC.symbol src_arr) sym str (Restructure.makeShifter bac 1) bac
  return $ PrefixBAC bac'

interpolateObject :: Chain -> (String, String) -> PrefixBAC -> Maybe PrefixBAC
interpolateObject chain (str1, str2) pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str1
  guard $ null $ searchString pbac str2
  let arr_arr = getArrow2 chain
  let sym = BAC.target (fst arr_arr) |> BAC.symbols |> maximum |> (+ 1)
  let dict = BAC.target (snd arr_arr) |> BAC.symbols |> fmap (\s -> (s, s+1)) |> Map.fromList
  bac' <- Add.addParentNode (BAC.symbol2 arr_arr) sym dict (str1, str2) (Restructure.makeShifter bac 1) bac
  return $ PrefixBAC bac'

prefixes :: Chain -> [(Chain, Chain)]
prefixes (Chain arr0 arrs) =
  BAC.prefix (BAC.target arr0) (BAC.symbol (last (arr0 : arrs)))
  |> fmap \(edge, arr) -> (Chain arr0 [edge], fromArrow2 (arr0 `BAC.join` edge, arr))

suffixes :: Chain -> [(Chain, Chain)]
suffixes (Chain arr0 arrs) =
  BAC.suffix (BAC.target arr0) (BAC.symbol (last (arr0 : arrs)))
  |> fmap \(arr, edge) -> (fromArrow2 (arr0, arr), Chain (arr0 `BAC.join` edge) [edge])

partitionPrefixesSuffixes :: Chain -> [([(Chain, Chain)], [(Chain, Chain)])]
partitionPrefixesSuffixes chain =
  Split.partitionPrefixesSuffixes src_node tgt_sym
  |> fmap (fmap toPrefix `bimap` fmap toSuffix)
  |> (++ (BAC.edges src_node
    |> filter (BAC.symbol .> (== tgt_sym))
    |> fmap (\edge -> Chain src_arr [edge])
    |> fmap \dchain -> ([(dchain, tgt)], [(src, dchain)])))
  where
  (src_arr, tgt_arr) = getArrow2 chain
  src_node = BAC.target src_arr
  tgt_sym = BAC.symbol tgt_arr
  toPrefix (edge, arr) = (Chain src_arr [edge], fromArrow2 (src_arr `BAC.join` edge, arr))
  toSuffix (arr, edge) = (fromArrow2 (src_arr, arr), Chain (src_arr `BAC.join` arr) [edge])
  src = id $ source chain
  tgt = id $ target chain

unsplittable :: Chain -> Chain -> Bool
unsplittable chain1 chain2 =
  chain1 ==~ chain2 && (length chain1 == 0 || sameGroup)
  where
  (pref1, suff1) = fromJust $ split 1 chain1
  (pref2, suff2) = fromJust $ split 1 chain2
  sameGroup =
    partitionPrefixesSuffixes chain1
    |> fmap fst
    |> find (any \(pref, suff) -> pref === pref1 && suff ==~ suff1)
    |> fromJust
    |> any \(pref, suff) -> pref === pref2 && suff ==~ suff2

swing :: Chain -> [Chain]
swing = partitionPrefixesSuffixes .> fmap (fst .> head .> uncurry concat .> fromJust)

splitMorphism :: PrefixBAC -> [[Chain]] -> Maybe PrefixBAC
splitMorphism (PrefixBAC bac) partition = do
  guard $ partition |> any notNull
  let chain = partition |> List.concat |> head
  let arr_arr = getArrow2 chain
  let (src_sym, tgt_sym) = BAC.symbol2 arr_arr
  guard $ src_sym /= BAC.base
  let src_node = BAC.target (fst arr_arr)
  let sym = src_node |> BAC.symbols |> maximum |> (+1)

  let groups = partitionPrefixesSuffixes chain |> fmap fst
  partition_groups <-
    partition
    |> traverse (traverse (split 1))
    >>= traverse (traverse \(pref, suff) ->
      groups |> find (any \(pref', suff') -> pref' === pref && suff' ==~ suff))
  let partition' =
        partition_groups
        |> fmap List.concat
        |> fmap (fmap (both (getArrow2 .> snd .> BAC.symbol)))
        |> fmap (filter (snd .> (/= BAC.base)))
        |> fmap nubSort
        |> zip [sym..]

  let direct_syms =
        src_node
        |> BAC.edges
        |> filter (BAC.symbol .> (== tgt_sym))
        |> fmap ((: []) .> Chain (fst arr_arr))
        |> fmap (\chain -> partition |> findIndices (any (=== chain)))
        |> fmap (fmap (fromIntegral .> (sym +)))
  guard $ direct_syms |> all (List.length .> (== 1))
  let direct' = direct_syms |> fmap head

  bac' <- Split.splitSymbol (src_sym, tgt_sym) partition' direct' bac
  return $ PrefixBAC bac'

paritionIncoming :: PrefixBAC -> Node -> [[Chain]]
paritionIncoming pbac tgt = partitionPrefixesSuffixes (init pbac tgt) |> fmap (snd .> fmap snd)

splitObjectIncoming :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, [String] -> [[String]])
splitObjectIncoming pnode@(Node src_arr) partition pbac@(PrefixBAC bac) = do
  guard $ partition |> fmap fst |> allComb (\a b -> isNothing $ comparePrefix a b)
  guard $ partition |> fmap fst |> all (searchString pbac .> null)
  guard $ partition |> any (snd .> notNull)
  let src_sym = BAC.symbol src_arr
  let sym = bac |> BAC.symbols |> maximum |> (+1)

  let groups = partitionPrefixesSuffixes (init pbac pnode)
  partition_groups <-
    partition
    |> fmap (fmap (fmap \chain -> fromJust $ init pbac (source chain) `concat` chain))
    |> traverse (snd .> traverse (split 1))
    >>= traverse (traverse \(pref, suff) ->
      groups |> find (fst .> any \(pref', suff') -> pref' === pref && suff' ==~ suff))
  let partition' =
        partition_groups
        |> fmap (fmap fst .> List.concat)
        |> fmap (fmap (both (getArrow2 .> snd .> BAC.symbol)))
        |> fmap (filter (snd .> (/= BAC.base)))
        |> fmap nubSort
        |> zip [sym..]

  let direct_syms =
        bac
        |> BAC.edges
        |> filter (BAC.symbol .> (== src_sym))
        |> fmap ((: []) .> Chain (BAC.root bac))
        |> fmap (\chain -> partition |> findIndices (snd .> any (=== chain)))
        |> fmap (fmap (fromIntegral .> (sym +)))
  guard $ direct_syms |> all (List.length .> (== 1))
  let direct' = direct_syms |> fmap head

  bac' <- Split.splitSymbol (BAC.base, src_sym) partition' direct' bac
  let bac'' =
        partition
        |> fmap fst
        |> zip [sym..]
        |> foldl (\node (sym, pref) -> modifyOutgoingValues sym (pref ++) node) bac'

  let incoming =
        partition_groups
        |> fmap (fmap (snd .> fmap snd))
        |> fmap List.concat
        |> zip (fmap fst partition)
        |> concatMap sequence
        |> fmap (fmap \(Chain _ arrs) -> head arrs |> BAC.value)
        |> fmap swap
        |> Map.fromList
  let outgoing = src_arr |> BAC.target |> BAC.edges |> fmap BAC.value
  let updater tokens =
        case (
          incoming |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          outgoing |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (_, Nothing) ->
            [tokens]
          (Just i, Just j) -> -- i + 1 == j
            [take j tokens ++ [incoming ! (tokens !! i) ++ tokens !! j] ++ drop (j + 1) tokens]
          (Nothing, Just j) -> -- j + 1 == List.length tokens
            partition
            |> fmap fst
            |> fmap \pref -> take j tokens ++ [pref ++ tokens !! j] ++ drop (j + 1) tokens

  return (PrefixBAC bac'', updater)

partitionOutgoing :: Node -> [[Chain]]
partitionOutgoing (Node arr) =
  Split.partitionSymbols src_node
  |> fmap (concatMap \sym -> BAC.edges src_node |> filter (BAC.symbol .> (== sym)))
  |> fmap (fmap ((: []) .> Chain arr))
  where
  src_node = BAC.target arr

splitObjectOutgoing :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, [String] -> [[String]])
splitObjectOutgoing pnode@(Node tgt_arr) partition (PrefixBAC bac) = do
  let tgt_sym = BAC.symbol tgt_arr
  guard $ tgt_sym /= BAC.base

  guard $ partition |> all (snd .> all (source .> (==- pnode)))
  let partition' = partition |> fmap (snd .> concatMap (getArrow2 .> snd .> BAC.dict .> Map.elems))
  let splitters = [0..] |> take (List.length partition) |> fmap (Restructure.makeShifter bac)

  bac' <- Split.splitNode tgt_sym (splitters `zip` partition') bac
  let syms = splitters |> fmap \splitter -> splitter (BAC.base, tgt_sym)
  let bac'' =
        partition
        |> fmap fst
        |> zip syms
        |> foldl (\node (sym, suff) -> modifyIncomingValues sym (++ suff) node) bac'

  let outgoing =
        partition'
        |> fmap (concatMap \sym -> BAC.target tgt_arr |> BAC.edges |> filter (BAC.symbol .> (== sym)))
        |> fmap (fmap BAC.value)
        |> zip (fmap fst partition)
        |> concatMap sequence
        |> fmap swap
        |> Map.fromList
  let incoming = BAC.suffix bac tgt_sym |> fmap (snd .> BAC.value)
  let updater tokens =
        case (
          incoming |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          outgoing |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, _) ->
            [tokens]
          (Just i, Just j) -> -- i + 1 == j
            [take i tokens ++ [tokens !! i ++ outgoing ! (tokens !! j)] ++ drop (i + 1) tokens]
          (Just i, Nothing) -> -- i == 0
            partition
            |> fmap fst
            |> fmap \suff -> take i tokens ++ [tokens !! i ++ suff] ++ drop (i + 1) tokens

  return (PrefixBAC bac'', updater)

splitCategory :: [[Chain]] -> PrefixBAC -> Maybe [PrefixBAC]
splitCategory partition pbac@(PrefixBAC bac) = do
  guard $ partition |> all (all (source .> (==- root pbac)))
  let partition' = partition |> fmap (concatMap (getArrow2 .> snd .> BAC.dict .> Map.elems))
  bacs' <- Split.splitRootNode partition' bac
  return $ fmap PrefixBAC bacs'

mergeMorphsisms :: [Chain] -> PrefixBAC -> Maybe PrefixBAC
mergeMorphsisms chains (PrefixBAC bac) = do
  let arr_arrs = chains |> fmap getArrow2
  guard $ notNull arr_arrs
  guard $ arr_arrs |> fmap (fst .> BAC.symbol) |> allSame
  let src_sym = arr_arrs |> head |> fst |> BAC.symbol
  guard $ src_sym /= BAC.base
  let tgt_syms = arr_arrs |> fmap (snd .> BAC.symbol)
  bac' <- Merge.mergeSymbols (src_sym, tgt_syms) (head tgt_syms) bac
  return $ PrefixBAC bac'

outgoingCanonicalOrders :: PrefixBAC -> Node -> [[Chain]]
outgoingCanonicalOrders _ (Node arr) =
  Zip.canonicalizeArrow arr
  |> fmap (fmap \sym ->
    BAC.target arr
    |> BAC.edges
    |> find (BAC.symbol .> (== sym))
    |> fromJust
    |> (: [])
    |> Chain arr
  )

incomingCanonicalOrders :: PrefixBAC -> Node -> [[Chain]]
incomingCanonicalOrders (PrefixBAC bac) (Node arr) =
  Zip.canonicalizeSuffixND bac (BAC.symbol arr)
  |> fmap (fmap (fromSymbol2 bac .> fromJust))

findOutgoingZippableObjects :: PrefixBAC -> Node -> [(Node, [[Chain]])]
findOutgoingZippableObjects (PrefixBAC bac) (Node arr) =
  Zip.unifiable bac (BAC.symbol arr)
  |> fromJust
  |> Map.toList
  |> fmap (first (BAC.arrow bac .> fromJust))
  |> fmap \(arr, orders) ->
    orders
    |> fmap (fmap \sym ->
      BAC.target arr
      |> BAC.edges
      |> find (BAC.symbol .> (== sym))
      |> fromJust
      |> (: [])
      |> Chain arr
    )
    |> (Node arr,)

findIncomingZippableObjects :: PrefixBAC -> Node -> [(Node, [[Chain]])]
findIncomingZippableObjects (PrefixBAC bac) (Node arr) =
  Zip.zippable bac (BAC.symbol arr)
  |> fromJust
  |> Map.toList
  |> fmap (first (BAC.arrow bac .> fromJust .> Node))
  |> fmap (fmap (fmap (fmap (fromSymbol2 bac .> fromJust))))

mergeObjectsIncoming :: [(Node, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
mergeObjectsIncoming pnode_outgoings (PrefixBAC bac) = do
  guard $ pnode_outgoings |> all \(Node arr, order) ->
    order |> all (getArrow2 .> fst .> BAC.symbol .> (== BAC.symbol arr))
  let pnode_orders =
        pnode_outgoings
        |> fmap (fmap (fmap (getArrow2 .> snd .> BAC.symbol)))
  guard $ pnode_orders |> all \(Node arr, order) ->
    BAC.target arr |> BAC.edgesND |> fmap BAC.symbol |> nubSort |> (== sort order)
  let sym_mappings =
        pnode_orders
        |> fmap \(Node arr, order) -> (BAC.symbol arr, Zip.canonicalMapping arr order)
  let syms = fmap fst sym_mappings

  bac' <- foldrM (uncurry Restructure.relabel) bac sym_mappings
  bac'' <- Zip.unifyNodes syms bac'
  bac''' <- Merge.mergeSymbolsOnRoot syms (head syms) bac''
  return $ PrefixBAC bac'''

mergeObjectsOutgoing :: [(Node, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
mergeObjectsOutgoing pnode_incomings (PrefixBAC bac) = do
  let sym_orderings =
        pnode_incomings
        |> fmap (fmap (fmap (getArrow2 .> BAC.symbol2)))
        |> fmap (first \(Node arr) -> BAC.symbol arr)
  let offsets =
        pnode_incomings
        |> fmap fst
        |> fmap (\(Node arr) -> BAC.target arr |> BAC.symbols |> maximum)
        |> scanl (+) 0
        |> (0 :)
        |> take (List.length pnode_incomings)
  let sym_mappings =
        zip pnode_incomings offsets
        |> fmap \((Node arr, _), offset) ->
          BAC.target arr
          |> BAC.symbols
          |> fmap (\sym -> (sym, if sym /= BAC.base then sym + offset else sym))
          |> Map.fromList
          |> (BAC.symbol arr,)

  bac' <- foldrM (uncurry Restructure.relabel) bac sym_mappings
  bac'' <- Merge.mergeNodes sym_orderings (snd .> head) bac'
  return $ PrefixBAC bac''

mergeCategories :: [PrefixBAC] -> Maybe PrefixBAC
mergeCategories pbacs = do
  let bacs = pbacs |> fmap (\(PrefixBAC bac) -> bac)
  let syms = bacs |> fmap (
        BAC.arrows
        .> concatMap (BAC.target .> BAC.edges)
        .> fmap BAC.value)
  guard $ syms |> allComb \a b ->
    a |> all \s ->
      b |> all \t ->
        comparePrefix s t |> isNothing

  let offsets =
        bacs
        |> fmap (BAC.symbols .> maximum)
        |> scanl (+) 0
        |> (0 :)
        |> take (List.length bacs)
  let mappings =
        zip bacs offsets
        |> fmap \(bac, offset) ->
          BAC.symbols bac
          |> fmap (\sym -> (sym, if sym /= BAC.base then sym + offset else sym))
          |> Map.fromList

  bacs' <- mappings `zip` bacs |> traverse (uncurry (Restructure.relabel BAC.base))
  bac' <- Merge.mergeRootNodes bacs'
  return $ PrefixBAC bac'
