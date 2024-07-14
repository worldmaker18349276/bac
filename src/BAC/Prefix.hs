{-# LANGUAGE BlockArguments #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use null" #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant id" #-}
{-# LANGUAGE TupleSections #-}

module BAC.Prefix (
  PrefixOrdering (..),
  toOrdering,
  comparePrefix,
  strip,
  recover,
  PrefixBAC,
  Chain,
  Node,
  empty,
  fromBAC,
  getBAC,
  validate,
  searchString,
  fromString,
  fromStrings,
  getStrings,
  getPreString,
  root,
  source,
  target,
  id,
  init,
  outgoing,
  incoming,
  join,
  length,
  split,
  dividel,
  divider,
  (==-),
  (===),
  (==~),
  refine,
  addEdge,
  removeEdge,
  alterEdge,
  isNondecomposable,
  Cofraction,
  Fraction,
  AlternativeRule,
  isAlternativeRule,
  getAlternativeRules,
  needAlternativePathsBeforeRemovingMorphism,
  removeMorphism,
  ObjectAlternativeRule,
  isObjectAlternativeRule,
  getObjectAlternativeRules,
  needAlternativePathsBeforeRemovingObject,
  removeObject,
  DivisionRule,
  getPossibleDivisionRules,
  compatibleDivisionRule,
  addMorphism,
  addObject,
  interpolateObject,
  prefixes,
  suffixes,
  partitionPrefixesSuffixes,
  isUnsplittable,
  splitMorphism,
  partitionIncoming,
  splitObjectIncoming,
  partitionOutgoing,
  splitObjectOutgoing,
  splitCategory,
  findMergableChains,
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
import Data.Bifunctor (bimap, first, second)
import Data.Char (isPrint)
import Data.Foldable (find)
import Data.Foldable.Extra (foldrM)
import Data.Functor.Identity (Identity (..))
import Data.List (elemIndex, findIndices, sort)
import qualified Data.List as List
import Data.List.Extra (allSame, firstJust, notNull, nubSort, snoc, nubSortOn)
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Maybe (fromJust, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)
import GHC.Base (assert)
import Prelude hiding (id, init, length)
import qualified Prelude

import BAC.Base (Arrow, BAC, Symbol)
import qualified BAC.Base as BAC
import qualified BAC.Fundamental.Add as Add
import qualified BAC.Fundamental.Merge as Merge
import qualified BAC.Fundamental.Remove as Remove
import qualified BAC.Fundamental.Restructure as Restructure
import qualified BAC.Fundamental.Split as Split
import qualified BAC.Fundamental.Zip as Zip
import Utils.Utils ((.>), (|>), guarded)
import qualified BAC.Fundamental.Fraction as Fraction


splice :: Int -> Int -> [a] -> [a] -> [a]
splice from to elems list = take from list ++ elems ++ drop to list

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

recover :: String -> PrefixOrdering -> String
recover str Equal = str
recover str (GreaterBy suff) = take (List.length str - List.length suff) str
recover str (LessBy suff) = str ++ suff

newtype PrefixBAC = PrefixBAC (BAC String)

data Chain = Chain (Arrow String) [Arrow String]

newtype Node = Node (Arrow String)

allComb :: (a -> a -> Bool) -> [a] -> Bool
allComb _ [] = True
allComb f (h:t) = all (f h) t && allComb f t

empty :: PrefixBAC
empty = PrefixBAC BAC.empty

fromBAC :: BAC String -> Maybe PrefixBAC
fromBAC bac = do
  let values = BAC.arrows bac
        |> concatMap (BAC.target .> BAC.edges)
        |> fmap BAC.value
  guard $ values |> all (all isPrint)
  guard $ values |> any (elem ' ') |> not
  guard $ values |> allComb \a b -> isNothing (a `comparePrefix` b)
  return $ PrefixBAC bac

getBAC :: PrefixBAC -> BAC String
getBAC (PrefixBAC bac) = bac

validate :: PrefixBAC -> Bool
validate (PrefixBAC bac) = BAC.validateAll bac

searchString :: PrefixBAC -> String -> [PrefixOrdering]
searchString (PrefixBAC bac) str =
  BAC.arrows bac
  |> concatMap (BAC.target .> BAC.edges)
  |> mapMaybe (BAC.value .> comparePrefix str)

followString :: BAC String -> String -> Maybe [Arrow String]
followString = go []
  where
  go res _node [] = Just res
  go res node str = node |> BAC.edges |> firstJust \edge -> do
    suff <- strip str (BAC.value edge)
    go (res `snoc` edge) (BAC.target edge) suff

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

followStrings :: BAC String -> [String] -> Maybe [Arrow String]
followStrings = go []
  where
  go res _node [] = Just res
  go res node (str:strs) = node |> BAC.edges |> firstJust \edge -> do
    guard $ BAC.value edge == str
    go (res `snoc` edge) (BAC.target edge) strs

fromStrings :: PrefixBAC -> [String] -> Maybe Chain
fromStrings _ [] = Nothing
fromStrings (PrefixBAC bac) strs = do
  arr0 <- findSource bac (head strs)
  chain <- followStrings (BAC.target arr0) strs
  return $ Chain arr0 chain
  where
  findSource :: BAC String -> String -> Maybe (Arrow String)
  findSource bac str =
    BAC.arrows bac
    |> find (BAC.target .> BAC.edges .> any (BAC.value .> (== str)))

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

join :: Chain -> Chain -> Maybe Chain
join chain1@(Chain arr0 arrs1) chain2@(Chain _ arrs2) = do
  guard $ target chain1 ==- source chain2
  return $ Chain arr0 (arrs1 ++ arrs2)

length :: Chain -> Int
length (Chain _ arrs) = List.length arrs

split :: Int -> Chain -> Maybe (Chain, Chain)
split index (Chain arr0 arrs) = do
  guard $ 0 <= index && index <= List.length arrs
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
  return $
    BAC.divide2 arr_arr2 arr_arr1
    |> fmap (fst arr_arr2,)
    |> fmap fromArrow2

(==-) :: Node -> Node -> Bool
(Node arr1) ==- (Node arr2) = BAC.symbol arr1 == BAC.symbol arr2

(===) :: Chain -> Chain -> Bool
chain1@(Chain arr1 _) === chain2@(Chain arr2 _) =
  BAC.symbol arr1 == BAC.symbol arr2 && getStrings chain1 == getStrings chain2

(==~) :: Chain -> Chain -> Bool
chain1 ==~ chain2 = BAC.symbol2 (getArrow2 chain1) == BAC.symbol2 (getArrow2 chain2)

updateChainBy :: (Functor m, Foldable m) => BAC String -> ((Symbol, [String]) -> m (Symbol, [String])) -> Chain -> m Chain
updateChainBy bac f chain =
  f (getArrow2 chain |> fst |> BAC.symbol, getStrings chain)
  |> fmap (fromSymbolAndStrings bac .> fromJust)
  where
  fromSymbolAndStrings :: BAC String -> (Symbol, [String]) -> Maybe Chain
  fromSymbolAndStrings bac (sym, strs) = do
    arr0 <- BAC.arrow bac sym
    chain <- followStrings (BAC.target arr0) strs
    return $ Chain arr0 chain

updateChainBy_ :: BAC String -> ((Symbol, [String]) -> (Symbol, [String])) -> Chain -> Chain
updateChainBy_ bac = noFoldable (updateChainBy bac)
  where
  noFoldable decorator f = runIdentity . decorator (Identity . f)

updateChain :: BAC String -> Chain -> Chain
updateChain bac = updateChainBy_ bac Prelude.id

updateChain_ :: BAC String -> Chain -> Chain
updateChain_ bac chain =
  fromJust $ fromPreStringAndStrings bac (getPreString chain, getStrings chain)
  where
  fromPreStringAndStrings :: BAC String -> (String, [String]) -> Maybe Chain
  fromPreStringAndStrings bac (prestr, strs) = do
    arrs0 <- followString bac prestr
    let arr0 = foldl BAC.join (BAC.root bac) arrs0
    chain <- followStrings (BAC.target arr0) strs
    return $ Chain arr0 chain

refine :: PrefixBAC -> (PrefixBAC, Chain -> Chain)
refine (PrefixBAC bac) = (PrefixBAC bac', updateChain_ bac')
  where
  syms_mapping = BAC.arrows bac |> fmap \arr ->
    BAC.target arr
    |> BAC.arrows
    |> fmap BAC.symbol
    |> reverse
    |> (`zip` [0 :: Symbol ..])
    |> Map.fromList
    |> (BAC.symbol arr,)
  bac' = syms_mapping |> foldl (\bac (sym, mapping) -> fromJust $ Restructure.relabel sym mapping bac) bac

addEdge :: Chain -> String -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
addEdge chain str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str
  bac' <- Restructure.addEdge (BAC.symbol2 (getArrow2 chain)) str bac
  return (PrefixBAC bac', updateChain bac')

removeEdge :: Chain -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Maybe Chain)
removeEdge chain@(Chain _ arrs) (PrefixBAC bac) = do
  guard $ List.length arrs == 1
  let arr_arr = getArrow2 chain
  let value = BAC.value (snd arr_arr)
  let edges = BAC.target (fst arr_arr) |> BAC.edges |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
  guard $ edges |> any (BAC.value .> (== value))
  bac' <- Restructure.removeEdge (BAC.symbol2 arr_arr) value bac
  let updater = updateChainBy bac' \(sym, tokens) ->
        if value `elem` tokens then Nothing else Just (sym, tokens)
  return (PrefixBAC bac', updater)

alterEdge :: Chain -> String -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
alterEdge chain@(Chain _ arrs) str (PrefixBAC bac) = do
  guard $ List.length arrs == 1
  let arr_arr = getArrow2 chain
  let value = BAC.value (snd arr_arr)
  let edges = BAC.target (fst arr_arr) |> BAC.edges |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
  guard $ edges |> any (BAC.value .> (== value))
  bac' <- Restructure.alterEdges (BAC.symbol2 arr_arr) (fmap \val -> if val == value then str else val) bac
  let updater = updateChainBy_ bac' $ second $ fmap \s -> if s == value then str else s
  return (PrefixBAC bac', updater)

isNondecomposable :: Chain -> Bool
isNondecomposable (Chain arr0 arrs) =
  List.length arrs == 1 && BAC.nondecomposable (BAC.target arr0) (BAC.symbol (head arrs))

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

type Cofraction = (Chain, Chain)
type Fraction = (Chain, Chain)
type AlternativeRule = ([Cofraction], [Fraction])

isAlternativeRule :: PrefixBAC -> Chain -> AlternativeRule -> Bool
isAlternativeRule pbac chain rule =
  (fst rule |> fmap (snd .> getStrings) |> sort |> (== incoming_strs))
  && (snd rule |> fmap (snd .> getStrings) |> sort |> (== outgoing_strs))
  && (fst rule |> all \(n, d) -> d `join` chain |> maybe False (==~ n))
  && (snd rule |> all \(n, d) -> chain `join` d |> maybe False (==~ n))
  && (fst rule |> all (fst .> getStrings .> notElem str))
  && (snd rule |> all (fst .> getStrings .> notElem str))
  where
  str = concat (getStrings chain)
  incoming_strs = chain |> source |> incoming pbac |> fmap getStrings |> sort
  outgoing_strs = chain |> target |> outgoing pbac |> fmap getStrings |> sort

getAlternativeRules :: PrefixBAC -> Chain -> Maybe ([([Chain], Chain)], [([Chain], Chain)])
getAlternativeRules pbac chain = do
  guard $ isNondecomposable chain
  let str = head $ getStrings chain
  let incoming_chains = chain |> source |> incoming pbac
  let outgoing_chains = chain |> target |> outgoing pbac
  
  let alt_paths :: String -> (Arrow String, Arrow String) -> [Chain]
      alt_paths skip_value (arr1, arr2) =
        go (BAC.target arr1) (BAC.symbol arr2) |> fmap (Chain arr1)
        where
        go node sym = if sym == BAC.base then return [] else do
          edge <- BAC.edges node
          guard $ BAC.value edge /= skip_value
          sym' <- BAC.dict edge |> Map.toList |> filter (snd .> (== sym)) |> fmap fst
          arrs <- go (BAC.target edge) sym'
          return $ edge : arrs
  let incoming_alts = incoming_chains |> fmap ((`join` chain) .> fromJust .> getArrow2 .> alt_paths str)
  let outgoing_alts = outgoing_chains |> fmap ((chain `join`) .> fromJust .> getArrow2 .> alt_paths str)
  return (incoming_alts `zip` incoming_chains, outgoing_alts `zip` outgoing_chains)

needAlternativePathsBeforeRemovingMorphism :: PrefixBAC -> Chain -> Maybe ([Chain], [Chain])
needAlternativePathsBeforeRemovingMorphism pbac@(PrefixBAC bac) chain = do
  guard $ isNondecomposable chain
  let sym = BAC.symbol2 (getArrow2 chain)
  let incoming_syms = chain |> target |> incoming pbac |> fmap (getArrow2 .> BAC.symbol2)
  let outgoing_syms = chain |> source |> outgoing pbac |> fmap (getArrow2 .> BAC.symbol2)

  let incoming_alts =
        Remove.relativeNondecomposablesIncoming bac sym
        |> filter (`notElem` incoming_syms)
        |> fmap (BAC.arrow2 bac .> fromJust .> fromArrow2)
  let outgoing_alts =
        Remove.relativeNondecomposablesOutgoing bac sym
        |> filter (`notElem` outgoing_syms)
        |> fmap (BAC.arrow2 bac .> fromJust .> fromArrow2)
  return (incoming_alts, outgoing_alts)

removeMorphism :: Chain -> AlternativeRule -> PrefixBAC -> Maybe (PrefixBAC, Chain -> [Chain])
removeMorphism chain rule pbac@(PrefixBAC bac) = do
  let arr_arr = getArrow2 chain

  guard $ isAlternativeRule pbac chain rule

  bac' <- Remove.removeNDSymbol (BAC.symbol2 arr_arr) bac

  let incoming =
        fst rule
        |> fmap (swap .> both getStrings .> first concat)
        |> Map.fromList
  let outgoing =
        snd rule
        |> fmap (swap .> both getStrings .> first concat)
        |> Map.fromList
  let removed =
        BAC.target (fst arr_arr)
        |> BAC.edges
        |> filter (BAC.symbol .> (== BAC.symbol (snd arr_arr)))
        |> fmap BAC.value
  let updateTokens tokens =
        case (
          incoming |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          removed |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          outgoing |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (_, Nothing, _) ->
            return tokens
          (Nothing, Just _, Nothing) ->
            assert (List.length tokens == 1)
              []
          (Just i, Just j, Nothing) ->
            assert (i + 1 == j && j + 1 == List.length tokens) $
              return $ splice i (j + 1) (incoming ! (tokens !! i)) tokens
          (Nothing, Just j, Just k) ->
            assert (j + 1 == k && j == 0) $
              return $ splice j (k + 1) (outgoing ! (tokens !! k)) tokens
          (Just i, Just j, Just k) ->
            assert (i + 1 == j && j + 1 == k) $
              [
                (incoming ! (tokens !! i)) `snoc` (tokens !! k),
                (tokens !! i) : (outgoing ! (tokens !! k))
              ]
              |> nubSort
              |> fmap \sub -> splice i (k + 1) sub tokens

  let updater = updateChainBy bac' (second updateTokens .> sequence)

  return (PrefixBAC bac', updater)

type ObjectAlternativeRule = [(Chain, (Chain, Chain))]

isObjectAlternativeRule :: PrefixBAC -> Node -> ObjectAlternativeRule -> Bool
isObjectAlternativeRule pbac node rule =
  (rule |> fmap (snd .> both getStrings) |> sort |> (== incoming_outgoing_strs))
  && (rule |> all \(n, (d1, d2)) -> d1 `join` d2 |> maybe False (==~ n))
  && (rule |> all (fst .> getStrings .> all \str -> str `notElem` concat outgoing_strs))
  where
  incoming_strs = node |> incoming pbac |> fmap getStrings |> sort
  outgoing_strs = node |> outgoing pbac |> fmap getStrings |> sort
  incoming_outgoing_strs = incoming_strs |> concatMap (\strs -> fmap (strs,) outgoing_strs) |> sort

getObjectAlternativeRules :: PrefixBAC -> Node -> [([Chain], (Chain, Chain))]
getObjectAlternativeRules pbac node = do
  let incoming_chains = incoming pbac node
  let outgoing_chains = outgoing pbac node
  chain1 <- incoming_chains
  chain2 <- outgoing_chains

  let incoming_strs = incoming_chains |> fmap (getStrings .> head)
  let alt_paths :: [String] -> (Arrow String, Arrow String) -> [Chain]
      alt_paths skip_values (arr1, arr2) =
        go (BAC.target arr1) (BAC.symbol arr2) |> fmap (Chain arr1)
        where
        go node sym = if sym == BAC.base then return [] else do
          edge <- BAC.edges node
          guard $ BAC.value edge `notElem` skip_values
          sym' <- BAC.dict edge |> Map.toList |> filter (snd .> (== sym)) |> fmap fst
          arrs <- go (BAC.target edge) sym'
          return $ edge : arrs

  let alt_chains = chain1 `join` chain2 |> fromJust |> getArrow2 |> alt_paths incoming_strs
  return (alt_chains, (chain1, chain2))

needAlternativePathsBeforeRemovingObject :: PrefixBAC -> Node -> [Chain]
needAlternativePathsBeforeRemovingObject (PrefixBAC bac) (Node arr) = do
  (sym1, sym2) <- Remove.relativeNondecomposables' bac (BAC.symbol arr)
  guard $ BAC.arrow bac sym1 |> fromJust |> BAC.target |> BAC.edges |> fmap BAC.symbol |> notElem sym2
  return $ BAC.arrow2 bac (sym1, sym2) |> fromJust |> fromArrow2

removeObject :: Node -> ObjectAlternativeRule -> PrefixBAC -> Maybe (PrefixBAC, Chain -> [Chain])
removeObject node@(Node arr) rule pbac@(PrefixBAC bac) = do
  bac' <- Remove.removeNode (BAC.symbol arr) bac

  guard $ isObjectAlternativeRule pbac node rule

  let outgoing = BAC.target arr |> BAC.edges |> fmap BAC.value
  let incoming = BAC.suffix bac (BAC.symbol arr) |> fmap (snd .> BAC.value)
  let alt = rule |> fmap (fmap (both (getStrings .> head)) .> swap .> fmap getStrings) |> Map.fromList
  let updater = updateChainBy bac' \(sym, tokens) ->
        case (
          incoming |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          sym == BAC.symbol arr,
          outgoing |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, True, Nothing) ->
            assert (null tokens)
              []
          (Nothing, False, Nothing) ->
            return (sym, tokens)
          (Just i, s, Just j) ->
            assert (i + 1 == j && s) $
              return (sym, splice i (j + 1) (alt ! (tokens !! i, tokens !! j)) tokens)
          _ ->
            []

  return (PrefixBAC bac', updater)


type DivisionRule = ([Cofraction], [Fraction])

getPossibleDivisionRules :: PrefixBAC -> Node -> Node -> Maybe ([[Cofraction]], [[Fraction]])
getPossibleDivisionRules (PrefixBAC bac) (Node src_arr) (Node tgt_arr) =
  Fraction.findValidCofractionsFractions (BAC.symbol src_arr) (BAC.symbol tgt_arr) bac
  |> fmap (both (fmap (fmap (both (fromSymbol2 bac .> fromJust)))))
  >>= guarded (uncurry (++) .> all notNull)

compatibleDivisionRule :: PrefixBAC -> DivisionRule -> Bool
compatibleDivisionRule (PrefixBAC bac) rule =
  Fraction.compatibleFractions bac (snd rule')
  && Fraction.compatibleCofractions bac (fst rule')
  && uncurry (Fraction.compatibleCofractionsFractions bac) rule'
  where
  rule' = rule |> both (fmap (both (getArrow2 .> BAC.symbol2)))

addMorphism :: Node -> Node -> DivisionRule -> String -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
addMorphism (Node src_arr) (Node tgt_arr) rule str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str
  guard $ BAC.symbol src_arr /= BAC.base
  let rule' = rule |> both (fmap (both (getArrow2 .> BAC.symbol2)))
  let sym = BAC.target src_arr |> BAC.symbols |> maximum |> (+ 1)
  bac' <- Add.addNDSymbol (BAC.symbol src_arr) (BAC.symbol tgt_arr) sym str (fst rule') (snd rule') bac
  return (PrefixBAC bac', updateChain bac')

addObject :: Node -> String -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
addObject (Node src_arr) str pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str
  let sym = BAC.target src_arr |> BAC.symbols |> maximum |> (+ 1)
  bac' <- Add.addLeafNode (BAC.symbol src_arr) sym str (Restructure.makeShifter bac 1) bac
  return (PrefixBAC bac', updateChain bac')

interpolateObject :: Chain -> (String, String) -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
interpolateObject chain (str1, str2) pbac@(PrefixBAC bac) = do
  guard $ null $ searchString pbac str1
  guard $ null $ searchString pbac str2
  let arr_arr = getArrow2 chain
  let sym = BAC.target (fst arr_arr) |> BAC.symbols |> maximum |> (+ 1)
  let dict = BAC.target (snd arr_arr) |> BAC.symbols |> fmap (\s -> (s, s+1)) |> Map.fromList
  bac' <- Add.addParentNode (BAC.symbol2 arr_arr) sym dict (str1, str2) (Restructure.makeShifter bac 1) bac
  return (PrefixBAC bac', updateChain bac')

prefixes :: Chain -> [(Chain, Chain)]
prefixes (Chain _ []) = []
prefixes chain =
  BAC.prefix (BAC.target arr0) (BAC.symbol arr1)
  |> fmap \(edge, arr) -> (Chain arr0 [edge], fromArrow2 (arr0 `BAC.join` edge, arr))
  where
  (arr0, arr1) = getArrow2 chain

suffixes :: Chain -> [(Chain, Chain)]
suffixes (Chain _ []) = []
suffixes chain =
  BAC.suffix (BAC.target arr0) (BAC.symbol arr1)
  |> fmap \(arr, edge) -> (fromArrow2 (arr0, arr), Chain (arr0 `BAC.join` arr) [edge])
  where
  (arr0, arr1) = getArrow2 chain

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

isUnsplittable :: Chain -> Chain -> Bool
isUnsplittable chain1 chain2 =
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

splitMorphism :: [[Chain]] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
splitMorphism partition (PrefixBAC bac) = do
  guard $ partition |> any notNull
  let chain = partition |> concat |> head
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
        |> fmap concat
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
  return (PrefixBAC bac', updateChain bac')

partitionIncoming :: PrefixBAC -> Node -> [[Chain]]
partitionIncoming pbac tgt = partitionPrefixesSuffixes (init pbac tgt) |> fmap (snd .> fmap snd)

splitObjectIncoming :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> [Chain])
splitObjectIncoming pnode@(Node src_arr) partition pbac@(PrefixBAC bac) = do
  guard $ partition |> fmap fst |> allComb (\a b -> isNothing $ comparePrefix a b)
  guard $ partition |> fmap fst |> all (searchString pbac .> null)
  guard $ partition |> any (snd .> notNull)
  let prefixes = fmap fst partition
  let src_sym = BAC.symbol src_arr
  let new_sym = bac |> BAC.symbols |> maximum |> (+1)

  let groups = partitionPrefixesSuffixes (init pbac pnode)
  partition_groups <-
    partition
    |> fmap (fmap (fmap \chain -> fromJust $ init pbac (source chain) `join` chain))
    |> traverse (snd .> traverse (split 1))
    >>= traverse (traverse \(pref, suff) ->
      groups |> find (fst .> any \(pref', suff') -> pref' === pref && suff' ==~ suff))
  let partition' =
        partition_groups
        |> fmap (fmap fst .> concat)
        |> fmap (fmap (both (getArrow2 .> snd .> BAC.symbol)))
        |> fmap (filter (snd .> (/= BAC.base)))
        |> fmap nubSort
        |> zip [new_sym..]

  let direct_syms =
        bac
        |> BAC.edges
        |> filter (BAC.symbol .> (== src_sym))
        |> fmap ((: []) .> Chain (BAC.root bac))
        |> fmap (\chain -> partition |> findIndices (snd .> any (=== chain)))
        |> fmap (fmap (fromIntegral .> (new_sym +)))
  guard $ direct_syms |> all (List.length .> (== 1))
  let direct' = direct_syms |> fmap head

  bac' <- Split.splitSymbol (BAC.base, src_sym) partition' direct' bac
  let bac'' =
        prefixes
        |> zip [new_sym..]
        |> foldl (\node (sym, pref) -> modifyOutgoingValues sym (pref ++) node) bac'

  let incoming =
        partition_groups
        |> fmap (fmap (snd .> fmap snd))
        |> fmap concat
        |> zip prefixes
        |> concatMap sequence
        |> fmap (fmap \(Chain _ arrs) -> head arrs |> BAC.value)
        |> fmap swap
        |> Map.fromList
  let outgoing = src_arr |> BAC.target |> BAC.edges |> fmap BAC.value
  let updater = updateChainBy bac'' \(sym, tokens) ->
        case (
          incoming |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          sym == src_sym,
          outgoing |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, False, Nothing) ->
            return (sym, tokens)
          (Nothing, True, Nothing) ->
            assert (null tokens) $
              take (List.length prefixes) [new_sym..] |> fmap (,tokens)
          (Just i, s, Nothing) ->
            assert (i + 1 == List.length tokens && not s) $
              return (sym, tokens)
          (Just i, s, Just j) ->
            assert (i + 1 == j && not s) $
              return (sym, splice j (j + 1) [incoming ! (tokens !! i) ++ tokens !! j] tokens)
          (Nothing, s, Just j) ->
            assert (j == 0 && s) $
              prefixes `zip` [new_sym..]
              |> fmap \(pref, sym') -> (sym', splice j (j + 1) [pref ++ tokens !! j] tokens)

  return (PrefixBAC bac'', updater)

partitionOutgoing :: Node -> [[Chain]]
partitionOutgoing (Node arr) =
  Split.partitionSymbols src_node
  |> fmap (concatMap \sym -> BAC.edges src_node |> filter (BAC.symbol .> (== sym)))
  |> fmap (fmap ((: []) .> Chain arr))
  where
  src_node = BAC.target arr

splitObjectOutgoing :: Node -> [(String, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> [Chain])
splitObjectOutgoing pnode@(Node tgt_arr) partition (PrefixBAC bac) = do
  let tgt_sym = BAC.symbol tgt_arr
  guard $ tgt_sym /= BAC.base

  guard $ partition |> all (snd .> all (source .> (==- pnode)))
  let suffixes = fmap fst partition
  let partition' = partition |> fmap (snd .> concatMap (getArrow2 .> snd .> BAC.dict .> Map.elems))
  let splitters = [0..] |> take (List.length partition) |> fmap (Restructure.makeShifter bac)

  bac' <- Split.splitNode tgt_sym (splitters `zip` partition') bac
  let new_syms = splitters |> fmap \splitter -> splitter (BAC.base, tgt_sym)
  let bac'' =
        suffixes
        |> zip new_syms
        |> foldl (\node (sym, suff) -> modifyIncomingValues sym (++ suff) node) bac'

  let outgoing =
        partition'
        |> fmap (concatMap \sym -> BAC.target tgt_arr |> BAC.edges |> filter (BAC.symbol .> (== sym)))
        |> fmap (fmap BAC.value)
        |> zip suffixes
        |> concatMap sequence
        |> fmap swap
        |> Map.fromList
  let incoming = BAC.suffix bac tgt_sym |> fmap (snd .> BAC.value)
  let updater = updateChainBy bac'' \(sym, tokens) ->
        case (
          incoming |> mapMaybe (`elemIndex` tokens) |> listToMaybe,
          sym == tgt_sym,
          outgoing |> Map.keys |> mapMaybe (`elemIndex` tokens) |> listToMaybe
        ) of
          (Nothing, False, _) ->
            return (sym, tokens)
          (Nothing, True, _) ->
            new_syms |> fmap (, tokens)
          (Just i, s, Just j) ->
            assert (i + 1 == j && not s) $
              return (sym, splice i (i + 1) [tokens !! i ++ outgoing ! (tokens !! j)] tokens)
          (Just i, s, Nothing) ->
            assert (i + 1 == List.length tokens && not s) $
              suffixes
              |> fmap \suff -> (sym, splice i (i + 1) [tokens !! i ++ suff] tokens)

  return (PrefixBAC bac'', updater)

splitCategory :: [[Chain]] -> PrefixBAC -> Maybe [PrefixBAC]
splitCategory partition pbac@(PrefixBAC bac) = do
  guard $ partition |> all (all (source .> (==- root pbac)))
  let partition' = partition |> fmap (concatMap (getArrow2 .> snd .> BAC.dict .> Map.elems))
  bacs' <- Split.splitRootNode partition' bac
  return $ fmap PrefixBAC bacs'

findMergableChains :: PrefixBAC -> Chain -> [Chain]
findMergableChains bac chain =
  BAC.target arr0
    |> BAC.arrows
    |> filter (BAC.dict .> Map.delete BAC.base .> (== dict0))
    |> filter (BAC.symbol .> (\sym -> fmap (! sym) incoming_dicts) .> (== mapping0))
    |> nubSortOn BAC.symbol
    |> fmap ((arr0,) .> fromArrow2)
  where
  (arr0, arr1) = getArrow2 chain
  dict0 = arr1 |> BAC.dict |> Map.delete BAC.base
  incoming_dicts = incoming bac (source chain) |> fmap (getArrow2 .> snd .> BAC.dict)
  sym0 = arr1 |> BAC.symbol
  mapping0 = fmap (! sym0) incoming_dicts

mergeMorphsisms :: [Chain] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
mergeMorphsisms chains (PrefixBAC bac) = do
  let arr_arrs = chains |> fmap getArrow2
  guard $ notNull arr_arrs
  guard $ arr_arrs |> fmap (fst .> BAC.symbol) |> allSame
  let src_sym = arr_arrs |> head |> fst |> BAC.symbol
  guard $ src_sym /= BAC.base
  let tgt_syms = arr_arrs |> fmap (snd .> BAC.symbol)
  bac' <- Merge.mergeSymbols (src_sym, tgt_syms) (head tgt_syms) bac
  return (PrefixBAC bac', updateChain bac')

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

mergeObjectsIncoming :: [(Node, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
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
  return (PrefixBAC bac''', updateChain_ bac''')

mergeObjectsOutgoing :: [(Node, [Chain])] -> PrefixBAC -> Maybe (PrefixBAC, Chain -> Chain)
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
  return (PrefixBAC bac'', updateChain_ bac'')

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
