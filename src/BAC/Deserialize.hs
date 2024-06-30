{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Deserialize (deserialize, deserializeWithValue) where

import Control.Applicative ((<|>))
import Control.Monad (guard, void)
import Data.Char (digitToInt)
import Data.Foldable (foldl')
import Data.List (sort)
import Data.List.Extra (allSame, groupSortOn, snoc)
import Data.Map (Map, fromList, insert, lookup, member)
import qualified Data.Map as Map
import Data.Map.Strict ((!))
import Data.Tuple.Extra (dupe)
import Text.Parsec
  ( ParseError,
    Parsec,
    anyToken,
    crlf,
    digit,
    eof,
    getState,
    many,
    many1,
    manyTill,
    newline,
    parserFail,
    runParser,
    setState,
    string',
  )
import Text.Parsec.Combinator (between)
import Prelude hiding (lookup)

import BAC.Base hiding (modify)
import Utils.Utils ((.>), (|>))

{- |
Deserialize a string to a BAC.

For example:

>>> import BAC.Examples
>>> import BAC.Serialize
>>> deserialize (serialize cone) == Right cone
True
>>> deserialize (serialize torus) == Right torus
True
>>> deserialize (serialize crescent) == Right crescent
True
-}
deserialize :: String -> Either ParseError (BAC ())
deserialize = runParser (parseNode parseEnd "" << eof) (ParserState mempty mempty) "" .> fmap fst

{- |
Deserialize a string to a BAC with value.

For example:

>>> import BAC.Examples
>>> import BAC.Serialize
>>> deserializeWithValue Just (serializeWithValue id cone') == Right cone'
True
>>> deserializeWithValue Just (serializeWithValue id torus') == Right torus'
True
>>> deserializeWithValue Just (serializeWithValue id crescent') == Right crescent'
True
-}
deserializeWithValue :: Monoid e => (String -> Maybe e) -> String -> Either ParseError (BAC e)
deserializeWithValue parse_value = runParser (parseNode (parseInlineValue parse_value) "" << eof) (ParserState mempty mempty) "" .> fmap fst

parseInlineValue :: (String -> Maybe e) -> Parsec String s e
parseInlineValue parser = do
  _ <- string' " "
  line <- manyTill anyToken parseEnd
  case parser line of
    Nothing -> parserFail "invalid value"
    Just val -> return val

parseInt :: Parsec String s Int
parseInt =
  many1 digit
  |> fmap (
    reverse
    .> zip [0 :: Int ..]
    .> fmap (fmap digitToInt .> \(i, n) -> 10 ^ i * n)
    .> sum
  )

parseEnd :: Parsec String s ()
parseEnd = void newline <|> void crlf <|> eof

infixr 2 <<
(<<) :: Monad m => m a -> m b -> m a
m << n = do
  a <- m
  _ <- n
  return a

parseDictElem :: String -> Parsec String s [Symbol]
parseDictElem indent =
  between (string' (indent ++ "[")) (string' "]") $ many do
    s <- parseInt
    _ <- string' ";"
    return $ fromIntegral s

parseRef :: String -> Parsec String s Int
parseRef indent = string' (indent ++ "&") >> parseInt << parseEnd

parseDeref :: String -> Parsec String s Int
parseDeref indent = string' (indent ++ "*") >> parseInt << parseEnd

type NodeSharedPtr = Int
type NodeUniquePtr = Int
data ParserState e = ParserState
  (Map NodeSharedPtr NodeUniquePtr)
  (Map NodeUniquePtr (BAC e, Map Symbol NodeUniquePtr))

parseEdge :: Monoid e => Parsec String (ParserState e) e -> String -> Parsec String (ParserState e) (Arrow e, Map Symbol NodeUniquePtr)
parseEdge value_parser indent = do
  elems <- parseDictElem indent
  val <- value_parser
  target <- parseTarget value_parser ("  " ++ indent)
  let keys = sort $ symbols (fst target)
  let dict = fromList (keys `zip` elems)
  case makeArrow dict val target of
    Nothing -> parserFail "invalid edge"
    Just arr -> return arr

rootDict :: BAC e -> (Dict, BAC e)
rootDict node = (symbols node |> fmap dupe |> Map.fromList, node)

extendDict :: (Dict, BAC e) -> [(Dict, BAC e)]
extendDict arr = edges (snd arr) |> fmap (\edge -> (fst arr `cat` dict edge, target edge))

arrowsDict :: BAC e -> [(Dict, BAC e)]
arrowsDict = rootDict .> go [] .> fmap snd
  where
  go res curr
    | sym `elem` fmap fst res = res
    | otherwise               = curr |> extendDict |> foldl' go res |> (`snoc` (sym, curr))
    where
    sym = fst curr ! base

makeArrow :: Dict -> e -> (BAC e, Map Symbol NodeUniquePtr) -> Maybe (Arrow e, Map Symbol NodeUniquePtr)
makeArrow arr_dict arr_value (arr_target, ptrs) = do
  -- check totality for this arrow.
  guard $ Map.keys arr_dict == symbols arr_target
  -- check supportivity for all paths prefixed with this arrow.
  guard $ arr_dict ! base /= base
  guard $
    arr_target
    |> arrowsDict
    |> fmap (\arr -> (arr_dict `cat` fst arr, ptrs ! (fst arr ! base)))
    |> groupSortOn (fst .> (! base))
    |> all allSame
  let ptrs' = ptrs |> Map.mapKeys (arr_dict !)
  return (Arrow {dict = arr_dict, value = arr_value, target = arr_target}, ptrs')

makeBAC :: [(Arrow e, Map Symbol NodeUniquePtr)] -> Parsec String (ParserState e) (BAC e, Map Symbol NodeUniquePtr)
makeBAC node_edges = do
  -- check supportivity for all edges.
  guard $
    node_edges
    |> concatMap (snd .> Map.toList)
    |> groupSortOn fst
    |> all allSame
  ParserState shared unique <- getState
  let ptr = length unique
  let ptrs' = node_edges |> concatMap (snd .> Map.toList) |> ((base, ptr) :) |> Map.fromList
  let res = (BAC (fmap fst node_edges), ptrs')
  let unique' = insert ptr res unique
  setState $ ParserState shared unique'
  return res

parseTarget :: Monoid e => Parsec String (ParserState e) e -> String -> Parsec String (ParserState e) (BAC e, Map Symbol NodeUniquePtr)
parseTarget value_parser indent =
  parseDerefnode indent
  <|> parseRefnode value_parser indent
  <|> parseNode value_parser indent

parseNode :: Monoid e => Parsec String (ParserState e) e -> String -> Parsec String (ParserState e) (BAC e, Map Symbol NodeUniquePtr)
parseNode value_parser indent = do
  edges <- many $ parseEdge value_parser indent
  makeBAC edges <|> parserFail "invalid node"

parseRefnode :: Monoid e => Parsec String (ParserState e) e -> String -> Parsec String (ParserState e) (BAC e, Map Symbol NodeUniquePtr)
parseRefnode value_parser indent = do
  ref <- parseRef indent
  res <- parseNode value_parser indent
  ParserState shared unique <- getState
  if ref `member` shared
  then
    parserFail "invalid ref"
  else do
    setState $ ParserState (insert ref (snd res ! base) shared) unique
    return res

parseDerefnode :: String -> Parsec String (ParserState e) (BAC e, Map Symbol NodeUniquePtr)
parseDerefnode indent = do
  deref <- parseDeref indent
  ParserState shared unique <- getState
  case lookup deref shared of
    Nothing -> parserFail "invalid deref"
    Just ptr -> return (unique ! ptr)
