{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified BAC.Base as BAC
import BAC.Deserialize (deserializeWithValue)
import BAC.Examples (cone')
import Console (Action (..), ConsoleState (..), Cursor (..), getBuffer, runAction, slotLength)
import Control.Exception (IOException, catch)
import Control.Monad (when)
import qualified Data.Either as Either
import Data.Either.Extra (maybeToEither)
import Data.Foldable (forM_)
import Data.Function ((&))
import Data.List.Extra (notNull, split)
import Data.Maybe (fromJust, fromMaybe, isNothing, listToMaybe)
import Interactive (Key (..), ModifiedKey (..), interact)
import Prefix (Chain)
import qualified Prefix
import System.Environment (getArgs)
import Prelude hiding (Left, Right, interact)

toAction :: ModifiedKey -> Maybe Action
toAction (ModifiedKey False False False Up)    = Just MoveUp
toAction (ModifiedKey False False False Down)  = Just MoveDown
toAction (ModifiedKey False False False Left)  = Just MoveLeft
toAction (ModifiedKey False False False Right) = Just MoveRight
toAction (ModifiedKey False True  False Up)    = Just DragUp      -- Alt-Up
toAction (ModifiedKey False True  False Down)  = Just DragDown    -- Alt-Down
toAction (ModifiedKey True  False False Up)    = Just SelectUp    -- Shift-Up
toAction (ModifiedKey True  False False Down)  = Just SelectDown  -- Shift-Down
toAction (ModifiedKey True  False False Left)  = Just SelectLeft  -- Shift-Left
toAction (ModifiedKey True  False False Right) = Just SelectRight -- Shift-Right
toAction (ModifiedKey False False False Enter) = Just NewSlot
toAction (ModifiedKey False False False (Char c)) = Just (Input [c])
toAction (ModifiedKey False False False Backspace) = Just DeleteBackward
toAction (ModifiedKey False True  False Backspace) = Just DeleteSlot -- Alt-Backspace
toAction (ModifiedKey False True  False (Char 'd')) = Just Dup -- Alt-'d'
toAction (ModifiedKey False True  False (Char 'j')) = Just Join -- Alt-'j'
toAction (ModifiedKey False True  False (Char 'k')) = Just ChangeType -- Alt-'k'
toAction (ModifiedKey False True  False (Char 'i')) = Just InitialChain -- Alt-'l'
toAction _ = Nothing

parseAction :: String -> Maybe Action
parseAction "MoveUp" = Just MoveUp
parseAction "MoveDown" = Just MoveDown
parseAction "MoveLeft" = Just MoveLeft
parseAction "MoveRight" = Just MoveRight
parseAction "DragUp" = Just DragUp
parseAction "DragDown" = Just DragDown
parseAction "SelectUp" = Just SelectUp
parseAction "SelectDown" = Just SelectDown
parseAction "SelectLeft" = Just SelectLeft
parseAction "SelectRight" = Just SelectRight
parseAction "NewSlot" = Just NewSlot
parseAction "DeleteBackward" = Just DeleteBackward
parseAction "DeleteSlot" = Just DeleteSlot
parseAction "Dup" = Just Dup
parseAction "Join" = Just Join
parseAction "ChangeType" = Just ChangeType
parseAction "InitialChain" = Just InitialChain
parseAction "IsNondecomposable" = Just IsNondecomposable
parseAction "AreSameMorphism" = Just AreSameMorphism
parseAction "AreUnsplittable" = Just AreUnsplittable
parseAction _ = Nothing

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

renderSlot range (Either.Right chain) = do
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
  let pretoken = Prefix.getPreString chain
  let pretoken' = if null pretoken then "(root)" else pretoken
  when (null tokens) $
    if isNothing range then
      putStr $ "\ESC[2m" ++ pretoken' ++ "\ESC[22m"
    else
      putStr $ "\ESC[2m\ESC[7m" ++ pretoken' ++ "\ESC[27m\ESC[22m"
  putStr "\ESC[m"

  putStrLn " "

getSubSelection :: ConsoleState -> Int -> Maybe (Int, Int)
getSubSelection (ConsoleState { buffer, cursor }) index
  | line cursor == lineFrom cursor && line cursor == index && column cursor /= columnFrom cursor
  = Just (min (column cursor) (columnFrom cursor), max (column cursor) (columnFrom cursor))
  | line cursor /= lineFrom cursor && lineFrom cursor <= index && index <= line cursor
  = Just (0, slotLength (buffer !! index))
  | line cursor /= lineFrom cursor && line cursor <= index && index <= lineFrom cursor
  = Just (0, slotLength (buffer !! index))
  | otherwise
  = Nothing

getCursorColumn :: ConsoleState -> Int
getCursorColumn (ConsoleState { buffer, cursor }) =
  buffer !! line cursor & \case
    Either.Left str -> column cursor
    Either.Right chain ->
      let
        tokens = Prefix.getStrings chain
        pretoken = Prefix.getPreString chain
        prelength
          | notNull tokens = 0
          | notNull pretoken = length pretoken
          | otherwise = length "(root)"
      in
        tokens & take (column cursor) & concat & length & (+ prelength)

renderConsoleState :: ConsoleState -> IO (Int, Int)
renderConsoleState state@(ConsoleState { buffer, cursor }) = do
  forM_ (buffer `zip` [0..]) \(slot, i) -> renderSlot (getSubSelection state i) slot
  putStrLn "───────────────────────────────────"
  return (line cursor, getCursorColumn state)

data Editor =
  ExploreMode {
    getConsole :: ConsoleState,
    getKey :: Maybe (Either String ModifiedKey),
    getAction :: Maybe Action,
    getMessages :: [String]
  }
  | CommandMode {
    getConsole :: ConsoleState,
    getInput :: (String, Int),
    getMessages :: [String]
  }

clear :: IO ()
clear = putStr "\ESC[2J\ESC[H"

moveCursor :: (Int, Int) -> IO ()
moveCursor (ln, col) = putStr $ "\ESC[" ++ show (ln + 1) ++ ";" ++ show (col + 1) ++ "H"

renderEditor :: Editor -> IO ()
renderEditor (ExploreMode state key action messages) = do
  clear
  pos <- renderConsoleState state
  case (key, action) of
    (Just key, Just action) ->
      putStrLn $ ": [" ++ either show show key ++ "] " ++ show action
    (Nothing, Just action) ->
      putStrLn $ ": " ++ show action
    (Just key, Nothing) ->
      putStrLn $ ": [" ++ either show show key ++ "]"
    (Nothing, Nothing) ->
      putStrLn ": "
  forM_ (fmap ("! " ++) messages) putStrLn
  moveCursor pos
renderEditor (CommandMode state (input, pos) messages) = do
  clear
  _ <- renderConsoleState state
  putStrLn $ ": " ++ input ++ " "
  forM_ (fmap ("! " ++) messages) putStrLn
  moveCursor (length (buffer state) + 1, pos + 2)

safeReadFile :: String -> IO (Either [String] String)
safeReadFile path =
  (Either.Right <$> readFile path) `catch` \(e :: IOException) -> do
    return $ Either.Left ["fail to read file: " ++ path | notNull path]

initialize :: String -> String -> IO Editor
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
  (prefix_bac, messages) <- case Prefix.fromBAC bac of
    Nothing ->
      return (fromJust $ Prefix.fromBAC BAC.empty, messages ++ ["not a prefix bac"])
    Just prefix_bac ->
      return (prefix_bac, messages)
  let buffer =
        strs_contents
        & split (== '\n')
        & fmap \str -> str & Prefix.fromString prefix_bac & maybeToEither str
  let state = ConsoleState { bac = prefix_bac, buffer, cursor = Cursor 0 0 0 0 }

  let editor = ExploreMode state Nothing Nothing messages
  renderEditor editor
  return editor

update :: Either String ModifiedKey -> Editor -> Maybe Editor
update (Either.Right (ModifiedKey False False False Esc)) editor@(ExploreMode {}) =
  Just $ CommandMode (getConsole editor) ("", 0) []
update (Either.Right (ModifiedKey False False False Esc)) editor@(CommandMode {}) =
  Just $ ExploreMode (getConsole editor) Nothing Nothing []
update key editor@(ExploreMode {}) = Just $ case fmap toAction key of
  Either.Left _ ->
    ExploreMode (getConsole editor) (Just key) Nothing []
  Either.Right Nothing ->
    ExploreMode (getConsole editor) (Just key) Nothing []
  Either.Right (Just action) ->
    case runAction action (getConsole editor) of
      Either.Left messages ->
        ExploreMode (getConsole editor) (Just key) (Just action) messages
      Either.Right next_state ->
        ExploreMode next_state (Just key) (Just action) []
update key editor@(CommandMode {}) = case key of
  Either.Right (ModifiedKey False False False Enter) -> case parseAction (fst (getInput editor)) of
    Nothing ->
      Just $ CommandMode (getConsole editor) (getInput editor) ["unknown command: " ++ fst (getInput editor)]
    Just action ->
      case runAction action (getConsole editor) of
        Either.Left messages ->
          Just $ ExploreMode (getConsole editor) Nothing (Just action) messages
        Either.Right next_state ->
          Just $ ExploreMode next_state Nothing (Just action) []
  Either.Right key -> case updateInput key (getInput editor) of
    Nothing ->
      Just $ CommandMode (getConsole editor) (getInput editor) ["invalid input"]
    Just input ->
      Just $ CommandMode (getConsole editor) input []
  _ ->
    Just $ CommandMode (getConsole editor) (getInput editor) ["invalid input"]

updateInput :: ModifiedKey -> (String, Int) -> Maybe (String, Int)
updateInput key (input, pos) = case key of
  ModifiedKey False False False (Char ch) ->
    Just (take pos input ++ [ch] ++ drop pos input, pos + 1)
  ModifiedKey False False False Backspace ->
    Just (take (pos - 1) input ++ drop pos input, max (pos - 1) 0)
  ModifiedKey False False False Delete ->
    let
      input' = take pos input ++ drop (pos + 1) input
      pos' = min pos (length input')
    in
      Just (input', pos')
  ModifiedKey False False False Left ->
    Just (input, max (pos - 1) 0)
  ModifiedKey False False False Right ->
    Just (input, min (pos + 1) (length input))
  _ -> Nothing

run :: Either String ModifiedKey -> Editor -> IO (Maybe Editor)
run key editor = case update key editor of
  Nothing -> return Nothing
  Just next_editor -> do
    renderEditor next_editor
    return $ Just next_editor

main :: IO ()
main = do
  args <- getArgs
  let bac_path = args & listToMaybe & fromMaybe ""
  let strs_path = drop 1 args & listToMaybe & fromMaybe ""
  state <- initialize bac_path strs_path
  interact run state
