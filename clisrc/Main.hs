{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified BAC.Base as BAC
import BAC.Deserialize (deserializeWithValue)
import BAC.Examples (cone')
import Console (ConsoleState (..), Cursor (..), Action (..), runMotion, getBuffer)
import Control.Exception (IOException, catch)
import Control.Monad (when)
import qualified Data.Either as Either
import Data.Either.Extra (maybeToEither)
import Data.Foldable (forM_)
import Data.List.Extra (notNull, split)
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
import Interactive (Key (..), ModifiedKey (..), interact)
import Prefix (Chain, fromBAC, fromString, getStrings)
import System.Environment (getArgs)
import Prelude hiding (Left, Right, interact)
import Data.Function ((&))

toAction :: ModifiedKey -> Maybe Action
toAction (ModifiedKey False False False Up)    = Just MoveUp
toAction (ModifiedKey False False False Down)  = Just MoveDown
toAction (ModifiedKey False False False Left)  = Just MoveLeft
toAction (ModifiedKey False False False Right) = Just MoveRight
toAction (ModifiedKey False True  False Up)    = Just DragUp      -- Alt-Up
toAction (ModifiedKey False True  False Down)  = Just DragDown    -- Alt-Down
toAction (ModifiedKey True  False False Left)  = Just SelectLeft  -- Shift-Left
toAction (ModifiedKey True  False False Right) = Just SelectRight -- Shift-Right
toAction (ModifiedKey False True  False (Char 'd')) = Just Dup    -- Alt-'d'
toAction (ModifiedKey False True  False Backspace) = Just Drop    -- Alt-Backspace
toAction (ModifiedKey False True  True  Backspace) = Just DropTop -- Alt-Ctrl-Backspace
toAction _ = Nothing

renderSlot :: Maybe (Int, Int) -> Either String Chain -> IO ()
renderSlot caret (Either.Left str) = do
  let (l, h) = case caret of
        Nothing -> (length str + 1, length str + 1)
        Just (from, to) -> (min from to, max from to)

  forM_ (str `zip` [0..]) \(ch, i) ->
    if l <= i && i < h then
      putStr ("\ESC[7m" ++ [ch] ++ "\ESC[27m")
    else
      putStr [ch]

  putStrLn " "

renderSlot caret (Either.Right chain) = do
  let tokens = getStrings chain
  let (l, h) = case caret of
        Nothing -> (length tokens + 1, length tokens + 1)
        Just (from, to) -> (min from to, max from to)

  putStr "\ESC[1m"
  forM_ (tokens `zip` [0..]) \(token, i) ->
    if l <= i && i < h then
      putStr ("\ESC[7m" ++ token ++ "\ESC[27m")
    else
      putStr token
  putStr "\ESC[m"

  putStrLn " "

renderConsoleState :: ConsoleState -> IO (Int, Int)
renderConsoleState state@(ConsoleState { memory, buffer, cursor }) = do
  let n0 = 0 :: Int
  forM_ (buffer `zip` [n0..]) \(slot, i) ->
    renderSlot (if line cursor == i then Just (column cursor, columnFrom cursor) else Nothing) slot
  putStrLn "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"
  let n1 = length buffer + 1
  forM_ (memory `zip` [n1..]) \(slot, i) ->
    renderSlot (if line cursor == i then Just (column cursor, columnFrom cursor) else Nothing) slot
  putStrLn "───────────────────────────────────"
  return (
      line cursor,
      getBuffer state & maybe 0 \case
        Either.Left str -> column cursor
        Either.Right chain -> getStrings chain & take (column cursor) & concat & length
    )

clear :: IO ()
clear = putStr "\ESC[2J\ESC[H"

moveCursor :: (Int, Int) -> IO ()
moveCursor (ln, col) = putStr $ "\ESC[" ++ show (ln + 1) ++ ";" ++ show (col + 1) ++ "H"

safeReadFile :: String -> IO (Either [String] String)
safeReadFile path =
  (Either.Right <$> readFile path) `catch` \(e :: IOException) -> do
    return $ Either.Left ["fail to read file: " ++ path | notNull path]

initialize :: String -> String -> IO ConsoleState
initialize bac_path strs_path = do
  let messages = ([] :: [String])

  (bac_contents, messages) <- safeReadFile bac_path
    & fmap (either
      (\msgs -> ("", messages ++ msgs))
      (, messages))
  (strs_contents, messages) <- safeReadFile strs_path
    & fmap (either
      (\msgs -> ("", messages ++ msgs))
      (, messages))

  (bac, messages) <- case deserializeWithValue Just bac_contents of
    Either.Left err ->
      return (BAC.empty, messages ++ ["fail to parse bac: " ++ show err])
    Either.Right bac ->
      return (bac, messages)
  (prefix_bac, messages) <- case fromBAC bac of
    Nothing ->
      return (fromJust $ fromBAC BAC.empty, messages ++ ["not a prefix bac"])
    Just prefix_bac ->
      return (prefix_bac, messages)
  let memory =
        strs_contents
        & split (== '\n')
        & filter notNull
        & fmap \str -> str & fromString prefix_bac & maybeToEither str
  let state = ConsoleState { bac = prefix_bac, buffer = [], memory, cursor = Cursor 0 0 0 }

  clear
  pos <- renderConsoleState state
  putStrLn ": "
  forM_ (fmap ("! " ++) messages) putStrLn
  moveCursor pos
  return state

run :: Either String ModifiedKey -> ConsoleState -> IO (Maybe ConsoleState)
run key state = do
  clear
  pos <- renderConsoleState next_state
  putStr $ ": [" ++ either show show key ++ "] " ++ action_str
  moveCursor pos
  return $ Just next_state
  where
  action = fmap toAction key
  action_str = either (const "UNKNOWN") (maybe "UNKNOWN" show) action
  next_state = case action of
    Either.Left _ -> state
    Either.Right Nothing -> state
    Either.Right (Just action) -> runMotion action state

main :: IO ()
main = do
  args <- getArgs
  let bac_path = args & listToMaybe & fromMaybe ""
  let strs_path = drop 1 args & listToMaybe & fromMaybe ""
  state <- initialize bac_path strs_path
  interact run state
