{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Render where

import Control.Monad (forM_, when)
import Data.Foldable.Extra (notNull)
import Data.List (findIndex, intersperse)
import Data.Maybe (fromJust, isNothing)

import qualified BAC.Prefix as Prefix
import Editor (Action, Editor (..), InputState (..), Status (..))
import Utils
import Workspace (Slot, Workspace (..), Cursor (..), slotLength)

renderSlot :: Maybe (Int, Int) -> Slot -> IO ()
renderSlot range (Left str) = do
  let (l, h) = case range of
        Nothing -> (length str + 1, length str + 1)
        Just (from, to) -> (min from to, max from to)

  forM_ (str `zip` [0..]) \(ch, i) ->
    if l <= i && i < h then
      putStr ("\ESC[7m" ++ [ch] ++ "\ESC[27m")
    else
      putStr [ch]

  putStrLn " "

renderSlot range (Right chain) = do
  let tokens = Prefix.getStrings chain
  let (from, to) = case range of
        Nothing -> (length tokens + 1, length tokens + 1)
        Just (from, to) -> (from, to)

  putStr "\ESC[1m"
  forM_ (tokens `zip` [0..]) \(token, i) ->
    if from <= i && i < to then
      putStr ("\ESC[7m" ++ token ++ "\ESC[27m")
    else
      putStr token
  let pretoken = "(" ++ Prefix.getPreString chain ++ ")"
  when (null tokens) $
    if isNothing range then
      putStr $ "\ESC[2m" ++ pretoken ++ "\ESC[22m"
    else
      putStr $ "\ESC[2m\ESC[7m" ++ pretoken ++ "\ESC[27m\ESC[22m"
  putStr "\ESC[m"

  -- for debug
  -- putStr $ "  (" ++ Prefix.getPreString chain ++ ";" ++ unwords tokens ++ ")"

  putStrLn " "

getSubSelection :: Workspace -> Int -> Maybe (Int, Int)
getSubSelection (Workspace { bank, cursor }) index
  | line cursor == lineFrom cursor && line cursor == index && column cursor /= columnFrom cursor
  = Just (min (column cursor) (columnFrom cursor), max (column cursor) (columnFrom cursor))
  | line cursor /= lineFrom cursor && lineFrom cursor <= index && index <= line cursor
  = Just (0, slotLength (bank !! index))
  | line cursor /= lineFrom cursor && line cursor <= index && index <= lineFrom cursor
  = Just (0, slotLength (bank !! index))
  | otherwise
  = Nothing

getCursorColumn :: Workspace -> Int
getCursorColumn (Workspace { bank, cursor }) =
  bank !! line cursor |> \case
    Left str -> column cursor
    Right chain ->
      let
        tokens = Prefix.getStrings chain
        pretoken = Prefix.getPreString chain
        prelength = if notNull tokens then 0 else length pretoken + 2
      in
        tokens |> take (column cursor) |> concat |> length |> (+ prelength)

renderWorkspace :: Workspace -> IO (Int, Int, Int)
renderWorkspace state@(Workspace { bank, cursor }) = do
  forM_ (bank `zip` [0..]) \(slot, i) -> renderSlot (getSubSelection state i) slot
  return (line cursor, getCursorColumn state, length bank)

msgPrefix :: String
msgPrefix = ""

renderStatus :: Status -> IO Int
renderStatus (Status key action messages) = do
  case (key, action) of
    (Just key, Just action) ->
      putStrLn $ ": [" ++ show key ++ "] " ++ show action
    (Nothing, Just action) ->
      putStrLn $ ": " ++ show action
    (Just key, Nothing) ->
      putStrLn $ ": [" ++ show key ++ "]"
    (Nothing, Nothing) ->
      putStrLn ": "
  forM_ (fmap (msgPrefix ++) messages) putStrLn
  return $ length messages + 1

renderInputState :: Action -> InputState a -> IO (Int, Int, Int)
renderInputState action (InputStringState hint _ input pos) = do
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  putStrLn $ input ++ " "
  return (1, pos, 2)
renderInputState action (InputSelectionState hint _ [] index) = do
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  putStrLn "\ESC[2m(no item to select)\ESC[22m"
  return (1, 0, 2)
renderInputState action (InputSelectionState hint _ options index) = do
  let strs =
        options
        |> fmap show
        |> zip [0..]
        |> fmap \(i, str) -> if i /= index then str else "\ESC[2m\ESC[7m" ++ str ++ "\ESC[27m\ESC[22m"
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  forM_ strs putStrLn
  return (index + 1, 0, length options + 1)
renderInputState action (InputPartitionState hint _ [] index) = do
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  putStrLn "\ESC[2m(no item to partition)\ESC[22m"
  return (1, 0, 2)
renderInputState action (InputPartitionState hint _ partition index) = do
  let strs =
        partition
        |> fmap (fmap show)
        |> intersperse ["┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"]
        |> concat
  let pos =
        partition
        |> fmap length
        |> scanl (+) 0
        |> tail
        |> findIndex (> index)
        |> fromJust
        |> (+ index)
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  putStrLn "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"
  forM_ strs putStrLn
  return (pos + 2, 0, sum (fmap length partition) + length partition + 1)


clear :: IO ()
clear = putStr "\ESC[2J\ESC[H"

moveCursor :: (Int, Int) -> IO ()
moveCursor (ln, col) = putStr $ "\ESC[" ++ show (ln + 1) ++ ";" ++ show (col + 1) ++ "H"

renderEditor :: Editor -> IO ()
renderEditor (ExploreMode state status) = do
  clear
  (ln, col, _) <- renderWorkspace state
  putStrLn "───────────────────────────────────"
  _ <- renderStatus status
  moveCursor (ln, col)
renderEditor (CommandMode state (input, pos) status) = do
  clear
  _ <- renderWorkspace state
  putStrLn "───────────────────────────────────"
  putStrLn $ ": " ++ input ++ " "
  forM_ (getMessages status |> fmap (msgPrefix ++)) putStrLn
  moveCursor (length (bank state) + 1, pos + 2)
renderEditor (InputMode state inputState curr_action status) = do
  clear
  (_, _, lines) <- renderWorkspace state
  putStrLn "───────────────────────────────────"
  (ln, col, _) <- renderInputState inputState curr_action
  putStrLn "───────────────────────────────────"
  _ <- renderStatus status
  moveCursor (lines + 1 + ln, col)

