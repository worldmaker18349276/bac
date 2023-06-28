{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Deserialize (deserialize) where

import Control.Applicative ((<|>))
import Control.Monad (void)
import Data.Char (digitToInt)
import Data.Map (Map, fromList, insert, lookup, member)
import Text.Parsec (Parsec, crlf, digit, eof, getState, many, many1, newline, parserFail,
  runParser, sepBy1, setState, string', ParseError)
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
deserialize :: String -> Either ParseError BAC
deserialize = runParser (parseNode "" << eof) mempty ""

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

parseDict :: String -> Parsec String s Dict
parseDict indent =
  string' (indent ++ "-") >> sepBy1 arrow (string' ";") << parseEnd |> fmap fromList
  where
  arrow = do
    _ <- string' " "
    s <- parseInt
    _ <- string' "->"
    r <- parseInt
    return (fromIntegral s, fromIntegral r)

parseRef :: String -> Parsec String s Int
parseRef indent = string' (indent ++ "&") >> parseInt << parseEnd

parseDeref :: String -> Parsec String s Int
parseDeref indent = string' (indent ++ "*") >> parseInt << parseEnd

parseEdge :: String -> Parsec String (Map Int BAC) Arrow
parseEdge indent = do
  dict <- parseDict indent
  target <- parseTarget ("  " ++ indent)
  case makeArrow dict target of
    Nothing -> parserFail "invalid edge"
    Just arr -> return arr

parseTarget :: String -> Parsec String (Map Int BAC) BAC
parseTarget indent =
  parseDerefnode indent
  <|> parseRefnode indent
  <|> parseNode indent

parseNode :: String -> Parsec String (Map Int BAC) BAC
parseNode indent = do
  edges <- many $ parseEdge indent
  case makeBAC edges of
    Nothing -> parserFail "invalid node"
    Just res -> return res

parseRefnode :: String -> Parsec String (Map Int BAC) BAC
parseRefnode indent = do
  ref <- parseRef indent
  res <- parseNode indent
  table <- getState
  if ref `member` table
  then
    parserFail "invalid ref"
  else do
    setState $ insert ref res table
    return res

parseDerefnode :: String -> Parsec String (Map Int BAC) BAC
parseDerefnode indent = do
  deref <- parseDeref indent
  table <- getState
  case lookup deref table of
    Nothing -> parserFail "invalid deref"
    Just res -> return res
