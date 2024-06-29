{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
module Main (main) where

import Prelude hiding (Right, Left, interact)
import Data.Foldable (forM_)

import Interactive (interact, ModifiedKey (..), Key (..))
import Console (ConsoleState (..), Motion (..), Cursor (..), runMotion)
import qualified Data.Either as Either
import Prefix (getStrings, Chain, fromBAC, fromString)
import Data.Maybe (fromJust)
import BAC.Examples (cone')

toMotion :: ModifiedKey -> Maybe Motion
toMotion (ModifiedKey False False False Up)    = Just MoveUp
toMotion (ModifiedKey False False False Down)  = Just MoveDown
toMotion (ModifiedKey False False False Left)  = Just MoveLeft
toMotion (ModifiedKey False False False Right) = Just MoveRight
toMotion (ModifiedKey False True  False Up)    = Just DragUp      -- Alt_Up
toMotion (ModifiedKey False True  False Down)  = Just DragDown    -- Alt_Down
toMotion (ModifiedKey True  False False Left)  = Just SelectLeft  -- Shift_Left
toMotion (ModifiedKey True  False False Right) = Just SelectRight -- Shift_Right
toMotion (ModifiedKey False True  False (Char 'd')) = Just Dup    -- Alt_D
toMotion (ModifiedKey False True  False Backspace) = Just Drop    -- Alt_Backspace
toMotion (ModifiedKey False True  True  Backspace) = Just DropTop -- Alt_Ctrl_Backspace
toMotion _ = Nothing

renderSlot :: Maybe (Int, Int) -> Either String Chain -> IO ()
renderSlot caret (Either.Left str) = do
  let (l, h) = case caret of
        Nothing -> (length str + 1, length str + 1)
        Just (from, to) -> (min from to, max from to)
    
  forM_ (str `zip` [0..]) \(ch, i) ->
    if l == i && l == h then
      putStr ("\ESC[4m" ++ [ch] ++ "\ESC[m")
    else if l <= i && i < h then
      putStr ("\ESC[7m" ++ [ch] ++ "\ESC[m")
    else
      putStr [ch]

  if length str == l && l == h then
    putStrLn "\ESC[4m \ESC[m"
  else
    putStrLn ""

renderSlot caret (Either.Right chain) = do
  let tokens = getStrings chain
  let (l, h) = case caret of
        Nothing -> (length tokens + 1, length tokens + 1)
        Just (from, to) -> (min from to, max from to)

  forM_ (tokens `zip` [0..]) \(token, i) ->
    if l == i && l == h then
      putStr ("\ESC[4m" ++ [head token] ++ "\ESC[m" ++ tail token)
    else if l <= i && i < h then
      putStr ("\ESC[7m" ++ token ++ "\ESC[m")
    else
      putStr token

  if length tokens == l && l == h then
    putStrLn "\ESC[4m \ESC[m"
  else
    putStrLn ""

render :: ConsoleState -> IO ()
render (ConsoleState { memory, buffer, cursor }) = do
  let n0 = 0 :: Int
  forM_ (buffer `zip` [n0..]) \(slot, i) ->
    renderSlot (if line cursor == i then Just (column cursor, columnFrom cursor) else Nothing) slot
  if line cursor == length buffer then
    putStrLn "\ESC[4m=\ESC[m=================================="
  else
    putStrLn "==================================="
  let n1 = length buffer + 1
  forM_ (memory `zip` [n1..]) \(slot, i) ->
    renderSlot (if line cursor == i then Just (column cursor, columnFrom cursor) else Nothing) slot

temp :: ConsoleState
temp = ConsoleState { bac, buffer, memory, cursor }
  where
  bac = fromJust $ fromBAC cone'
  buffer = [
    Either.Left "sdfese",
    Either.Left "sdfece",
    Either.Right $ fromJust $ fromString bac "0vvc1"
    ]
  memory = [
    Either.Right $ fromJust $ fromString bac "0vvc1cy",
    Either.Left "sssss",
    Either.Right $ fromJust $ fromString bac "0ppy"
    ]
  cursor = Cursor 0 0 0

clear :: IO ()
clear = putStr "\ESC[2J\ESC[H"

initialize :: String -> IO ConsoleState
initialize _path = do
  clear
  render temp
  return temp

run :: Either String ModifiedKey -> ConsoleState -> IO (Maybe ConsoleState)
run key state = do
  clear
  render next_state
  putStr $ "[" ++ either show show key ++ "]"
  return $ Just next_state
  where
  next_state = case fmap toMotion key of
    Either.Left _ -> state
    Either.Right Nothing -> state
    Either.Right (Just motion) -> runMotion motion state

repl :: String -> IO ()
repl path = do
  state <- initialize path
  interact run state

main :: IO ()
main = repl ""
