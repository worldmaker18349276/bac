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
  samePartitionGroup,
  swing,
  splitMorphism,
  paritionIncoming,
  splitObjectIncoming,
  partitionOutgoing,
  splitObjectOutgoing,
  splitCategory,
  mergeMorphsisms,
  outgoingNDOrders,
  incomingNDOrders,
  outgoingZippable,
  incomingZippable,
  mergeObjectIncoming,
  mergeObjectOutgoing,
) where

import Control.Monad (guard)
import Data.Bifunctor (bimap, first)
import Data.Foldable (find)
import Data.Foldable.Extra (foldrM)
import Data.List (findIndices, sort, uncons)
import qualified Data.List as List
import Data.List.Extra (allSame, firstJust, notNull, nubSort, snoc, unsnoc)
import qualified Data.Map as Map
import Data.Maybe (fromJust, isJust, isNothing, mapMaybe)
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
  guard $
    BAC.arrows bac
    |> concatMap (BAC.target .> BAC.edges)
    |> fmap BAC.value
    |> allComb (\a b -> isNothing (a `comparePrefix` b))
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

isNondecomposable :: Chain -> Bool
isNondecomposable (Chain arr0 arrs) =
  Prelude.length arrs == 1 && BAC.nondecomposable (BAC.target arr0) (BAC.symbol (head arrs))

removeMorphism :: Chain -> PrefixBAC -> Maybe PrefixBAC
removeMorphism chain (PrefixBAC bac) = do
  let arr_arr = getArrow2 chain
  guard $ fst arr_arr |> BAC.symbol |> (/= BAC.base)
  bac' <- Remove.removeNDSymbol (BAC.symbol2 arr_arr) bac
  return $ PrefixBAC bac'

removeObject :: Node -> PrefixBAC -> Maybe PrefixBAC
removeObject (Node arr) (PrefixBAC bac) = do
  bac' <- Remove.removeNode (BAC.symbol arr) bac
  return $ PrefixBAC bac'


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
  Split.partitionPrefixSuffix src_node tgt_sym
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

samePartitionGroup :: Chain -> Chain -> Bool
samePartitionGroup chain1 chain2 =
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

modifyOutgoingValues :: Monoid e => Symbol -> (e -> e) -> BAC e -> BAC e
modifyOutgoingValues sym f bac =
  fromJust $ BAC.fromInner $ BAC.root bac |> BAC.modifyUnder sym \(_curr, edge) -> \case
    BAC.AtOuter -> return edge
    BAC.AtBoundary -> return edge {BAC.target = tgt_node'}
    BAC.AtInner res -> return edge {BAC.target = res}
  where
  tgt_node = BAC.target $ fromJust $ BAC.arrow bac sym
  tgt_node' = tgt_node |> BAC.edges |> fmap (\edge -> edge {BAC.value = f (BAC.value edge)}) |> BAC.BAC

paritionIncoming :: PrefixBAC -> Node -> [[Chain]]
paritionIncoming pbac tgt = partitionPrefixesSuffixes (init pbac tgt) |> fmap (snd .> fmap snd)

splitObjectIncoming :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
splitObjectIncoming pnode@(Node src_arr) partition pbac@(PrefixBAC bac) = do
  guard $ partition |> fmap fst |> allComb (\a b -> isNothing $ comparePrefix a b)
  guard $ partition |> any (snd .> notNull)
  let src_sym = BAC.symbol src_arr
  let sym = bac |> BAC.symbols |> maximum |> (+1)

  let groups = partitionPrefixesSuffixes (init pbac pnode) |> fmap fst
  partition_groups <-
    partition
    |> fmap (fmap (fmap \chain -> fromJust $ init pbac (source chain) `concat` chain))
    |> traverse (snd .> traverse (split 1))
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
        |> foldl (\node (sym, suff) -> modifyOutgoingValues sym (++ suff) node) bac'
  return $ PrefixBAC bac''

partitionOutgoing :: Node -> [[Chain]]
partitionOutgoing (Node arr) =
  Split.partitionSymbols src_node
  |> fmap (concatMap \sym -> BAC.edges src_node |> filter (BAC.symbol .> (== sym)))
  |> fmap (fmap ((: []) .> Chain arr))
  where
  src_node = BAC.target arr

modifyIncomingValues :: Monoid e => Symbol -> (e -> e) -> BAC e -> BAC e
modifyIncomingValues sym f bac =
  fromJust $ BAC.fromInner $ BAC.root bac |> BAC.modifyUnder sym \(_curr, edge) -> \case
    BAC.AtOuter -> return edge
    BAC.AtBoundary -> return edge {BAC.value = f (BAC.value edge)}
    BAC.AtInner res -> return edge {BAC.target = res}

splitObjectOutgoing :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
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
  return $ PrefixBAC bac''

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

outgoingNDOrders :: PrefixBAC -> Node -> [[Chain]]
outgoingNDOrders _ (Node arr) =
  Zip.canonicalizeArrow arr
  |> fmap (fmap \sym ->
    BAC.target arr
    |> BAC.edges
    |> find (BAC.symbol .> (== sym))
    |> fromJust
    |> (: [])
    |> Chain arr
  )

incomingNDOrders :: PrefixBAC -> Node -> [[Chain]]
incomingNDOrders (PrefixBAC bac) (Node arr) =
  Zip.canonicalizeSuffixND bac (BAC.symbol arr)
  |> fmap (fmap (fromSymbol2 bac .> fromJust))

outgoingZippable :: PrefixBAC -> Node -> [(Node, [[Chain]])]
outgoingZippable (PrefixBAC bac) (Node arr) =
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

incomingZippable :: PrefixBAC -> Node -> [(Node, [[Chain]])]
incomingZippable (PrefixBAC bac) (Node arr) =
  Zip.zippable bac (BAC.symbol arr)
  |> fromJust
  |> Map.toList
  |> fmap (first (BAC.arrow bac .> fromJust .> Node))
  |> fmap (fmap (fmap (fmap (fromSymbol2 bac .> fromJust))))

mergeObjectIncoming :: [(Node, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
mergeObjectIncoming pnode_outgoings (PrefixBAC bac) = do
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

mergeObjectOutgoing :: [(Node, [Chain])] -> PrefixBAC -> Maybe PrefixBAC
mergeObjectOutgoing pnode_incomings (PrefixBAC bac) = do
  let sym_orderings =
        pnode_incomings
        |> fmap (fmap (fmap (getArrow2 .> BAC.symbol2)))
        |> fmap (first \(Node arr) -> BAC.symbol arr)
  bac' <- Merge.mergeNodes sym_orderings (snd .> head) bac
  return $ PrefixBAC bac'