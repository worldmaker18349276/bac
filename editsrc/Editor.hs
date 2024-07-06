{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
module Editor where

import Control.Applicative (Alternative)
import Control.Exception (IOException, catch)
import Control.Monad (MonadPlus, when)
import Control.Monad.Trans.Maybe (MaybeT (MaybeT, runMaybeT))
import Control.Monad.Trans.Reader (ReaderT (ReaderT, runReaderT))
import qualified Data.Either as Either
import Data.Either.Extra (maybeToEither)
import Data.Foldable (forM_, find)
import Data.Function ((&))
import Data.List (findIndex)
import Data.List.Extra (notNull, split)
import Data.Maybe (fromJust, fromMaybe, isNothing, listToMaybe)
import GHC.Base (Alternative (..))
import System.Environment (getArgs)
import Prelude hiding (Left, Right, interact)

import qualified BAC.Base as BAC
import BAC.Deserialize (deserializeWithValue)
import BAC.Prefix (Chain)
import qualified BAC.Prefix as Prefix
import Interactive (Key (..), ModifiedKey (..), interact)
import Workspace (Action (..), Cursor (..), Workspace (..), getBuffer, runAction, slotLength, Control (..), actions)
import Utils
import qualified Data.Map.Strict as Map

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
toAction (ModifiedKey False True  False Enter) = Just Search
toAction (ModifiedKey False False False (Char c)) = Just (Input [c])
toAction (ModifiedKey False False False Backspace) = Just DeleteBackward
toAction (ModifiedKey False True  False Backspace) = Just DeleteSlot -- Alt-Backspace
toAction (ModifiedKey False True  False (Char 'd')) = Just Dup -- Alt-'d'
toAction (ModifiedKey False True  False (Char 'j')) = Just Join -- Alt-'j'
toAction (ModifiedKey False True  False (Char 'k')) = Just ChangeType -- Alt-'k'
toAction (ModifiedKey False True  False (Char 'i')) = Just InitialChain -- Alt-'i'
toAction (ModifiedKey False True  False Left)  = Just SwingLeft  -- Alt-Left
toAction (ModifiedKey False True  False Right) = Just SwingRight -- Alt-Right
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

  -- for debug
  -- putStr $ "  (" ++ Prefix.getPreString chain ++ ";" ++ unwords tokens ++ ")"

  putStrLn " "

getSubSelection :: Workspace -> Int -> Maybe (Int, Int)
getSubSelection (Workspace { buffer, cursor }) index
  | line cursor == lineFrom cursor && line cursor == index && column cursor /= columnFrom cursor
  = Just (min (column cursor) (columnFrom cursor), max (column cursor) (columnFrom cursor))
  | line cursor /= lineFrom cursor && lineFrom cursor <= index && index <= line cursor
  = Just (0, slotLength (buffer !! index))
  | line cursor /= lineFrom cursor && line cursor <= index && index <= lineFrom cursor
  = Just (0, slotLength (buffer !! index))
  | otherwise
  = Nothing

getCursorColumn :: Workspace -> Int
getCursorColumn (Workspace { buffer, cursor }) =
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

renderWorkspace :: Workspace -> IO (Int, Int, Int)
renderWorkspace state@(Workspace { buffer, cursor }) = do
  forM_ (buffer `zip` [0..]) \(slot, i) -> renderSlot (getSubSelection state i) slot
  putStrLn "───────────────────────────────────"
  return (line cursor, getCursorColumn state, length buffer + 1)

data Editor =
  ExploreMode {
    getWorkspace :: Workspace,
    getKey :: Maybe (Either String ModifiedKey),
    getAction :: Maybe Action,
    getMessages :: [String]
  }
  | CommandMode {
    getWorkspace :: Workspace,
    getInput :: (String, Int),
    getMessages :: [String]
  }
  | InputMode {
    getWorkspace :: Workspace,
    getInputState :: InputState (InputControl (Either [String] Workspace)),
    getAction :: Maybe Action,
    getMessages :: [String]
  }

data InputState a where
  InputStringState :: (String -> a) -> String -> Int -> InputState a
  InputSelectionState :: Show b => (b -> a) -> [b] -> Int -> InputState a
  InputPartitionState :: Show b => ([[b]] -> a) -> [[b]] -> Int -> InputState a

createInputStringState :: (String -> a) -> InputState a
createInputStringState f = InputStringState f "" 0

createInputSelectionState :: Show b => (b -> a) -> [b] -> InputState a
createInputSelectionState f options = InputSelectionState f options 0

createInputPartitionState :: Show b => ([[b]] -> a) -> [b] -> InputState a
createInputPartitionState f partition = InputPartitionState f (fmap (: []) partition) 0

instance Functor InputState where
  fmap :: (a -> b) -> InputState a -> InputState b
  fmap f (InputStringState g val i) = InputStringState (g .> f) val i
  fmap f (InputSelectionState g val i) = InputSelectionState (g .> f) val i
  fmap f (InputPartitionState g val i) = InputPartitionState (g .> f) val i

data InputResult s a = Cancel | Finish a | Wait [String] s deriving (Functor)

-- free MonadPlus of InputState
newtype InputControl a = InputControl (InputResult (InputState (InputControl a)) a)

joinInputControl :: InputControl (InputControl a) -> InputControl a
joinInputControl (InputControl Cancel) = InputControl Cancel
joinInputControl (InputControl (Finish ctrl)) = ctrl
joinInputControl (InputControl (Wait messages state)) =
  InputControl $ Wait messages $ fmap joinInputControl state

instance Functor InputControl where
  fmap f (InputControl Cancel) = InputControl Cancel
  fmap f (InputControl (Finish a)) = InputControl $ Finish (f a)
  fmap f (InputControl (Wait messages state)) =
    InputControl $ Wait messages $ fmap (fmap f) state

instance Applicative InputControl where
  pure :: a -> InputControl a
  pure = InputControl . Finish
  (<*>) :: InputControl (a -> b) -> InputControl a -> InputControl b
  mf <*> ma = mf >>= (`fmap` ma)

instance Monad InputControl where
  (>>=) :: InputControl a -> (a -> InputControl b) -> InputControl b
  ctrl >>= f = fmap f ctrl |> joinInputControl

instance Alternative InputControl where
  empty :: InputControl a
  empty = InputControl Cancel
  (<|>) :: InputControl a -> InputControl a -> InputControl a
  InputControl Cancel <|> _ = InputControl Cancel
  _ <|> InputControl Cancel = InputControl Cancel
  ma <|> _ = ma

instance MonadPlus InputControl where

instance Control InputControl where
  inputString :: String -> InputControl String
  inputString hint = InputControl $ Wait [hint] $ createInputStringState return
  inputSelection :: Show a => String -> [a] -> InputControl a
  inputSelection hint options = InputControl $ Wait [hint] $ createInputSelectionState return options
  inputPartition :: Show a => String -> [a] -> InputControl [[a]]
  inputPartition hint partition = InputControl $ Wait [hint] $ createInputPartitionState return partition


clear :: IO ()
clear = putStr "\ESC[2J\ESC[H"

moveCursor :: (Int, Int) -> IO ()
moveCursor (ln, col) = putStr $ "\ESC[" ++ show (ln + 1) ++ ";" ++ show (col + 1) ++ "H"

renderEditor :: Editor -> IO ()
renderEditor (ExploreMode state key action messages) = do
  clear
  (ln, col, _) <- renderWorkspace state
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
  moveCursor (ln, col)
renderEditor (CommandMode state (input, pos) messages) = do
  clear
  _ <- renderWorkspace state
  putStrLn $ ": " ++ input ++ " "
  forM_ (fmap ("! " ++) messages) putStrLn
  moveCursor (length (buffer state) + 1, pos + 2)
renderEditor (InputMode state inputState action messages) = do
  clear
  (_, _, lines) <- renderWorkspace state
  (ln, col, _) <- renderInputState inputState
  putStrLn $ ": " ++ maybe "" show action
  forM_ (fmap ("! " ++) messages) putStrLn
  moveCursor (lines + ln, col)

renderInputState :: InputState a -> IO (Int, Int, Int)
renderInputState (InputStringState _ input pos) = do
  putStrLn $ input ++ " "
  putStrLn "───────────────────────────────────"
  return (0, pos, 2)
renderInputState (InputSelectionState _ options index) = do
  let strs =
        options
        |> fmap show
        |> zip [0..]
        |> fmap \(i, str) -> if i /= index then str else "\ESC[2m\ESC[7m" ++ str ++ "\ESC[27m\ESC[22m"
  forM_ strs putStrLn
  putStrLn "───────────────────────────────────"
  return (index, 0, length options + 1)
renderInputState (InputPartitionState _ partition index) = do
  let strs =
        partition
        |> fmap (fmap show)
        |> zip [0..]
        |> concatMap sequence
        |> fmap (\(i, str) -> if even i then str else "\ESC[7m" ++ str ++ "\ESC[27m")
        |> zip [0..]
        |> fmap \(i, str) -> if i /= index then str else "\ESC[2m" ++ str ++ "\ESC[22m"
  forM_ strs putStrLn
  putStrLn "───────────────────────────────────"
  return (index, 0, sum (fmap length partition) + 1)

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
  let state = Workspace { bac = prefix_bac, buffer, cursor = Cursor 0 0 0 0 }

  let editor = ExploreMode state Nothing Nothing messages
  renderEditor editor
  return editor

update :: Either String ModifiedKey -> Editor -> Maybe Editor

update (Either.Right (ModifiedKey False False False Esc)) editor@(ExploreMode {}) =
  Just $ CommandMode (getWorkspace editor) ("", 0) []
update key editor@(ExploreMode {}) = case fmap toAction key of
  Either.Left _ ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing []
  Either.Right Nothing ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing []
  Either.Right (Just action) -> do
    case runAction action (getWorkspace editor) of
      InputControl Cancel ->
        Just $ ExploreMode (getWorkspace editor) (Just key) (Just action) ["cancel"]
      InputControl (Finish (Either.Left messages)) ->
        Just $ ExploreMode (getWorkspace editor) (Just key) (Just action) messages
      InputControl (Finish (Either.Right next_state)) ->
        Just $ ExploreMode next_state (Just key) (Just action) []
      InputControl (Wait messages state) ->
        Just $ InputMode (getWorkspace editor) state (Just action) messages

update key editor@(CommandMode {}) = case updateInputStringSlot key (getInput editor) of
  Cancel ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing []
  Wait messages input ->
    Just $ CommandMode (getWorkspace editor) input messages
  Finish input -> case find (show .> (== input)) actions of
    Nothing ->
      Just $ CommandMode (getWorkspace editor) (getInput editor) ["unknown command: " ++ fst (getInput editor)]
    Just action -> do
      case runAction action (getWorkspace editor) of
        InputControl Cancel ->
          Just $ ExploreMode (getWorkspace editor) (Just key) (Just action) ["cancel"]
        InputControl (Finish (Either.Left messages)) ->
          Just $ ExploreMode (getWorkspace editor) Nothing (Just action) messages
        InputControl (Finish (Either.Right next_state)) ->
          Just $ ExploreMode next_state Nothing (Just action) []
        InputControl (Wait messages state) ->
          Just $ InputMode (getWorkspace editor) state (Just action) messages

update key editor@(InputMode {}) = case updateInputState key (getInputState editor) of
  Cancel ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing ["cancel action"]
  Wait messages state ->
    Just $ InputMode (getWorkspace editor) state (getAction editor) messages
  Finish (InputControl Cancel) ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing ["cancel action"]
  Finish (InputControl (Wait messages state)) ->
    Just $ InputMode (getWorkspace editor) state (getAction editor) messages
  Finish (InputControl (Finish (Either.Left messages))) ->
    Just $ ExploreMode (getWorkspace editor) (Just key) Nothing messages
  Finish (InputControl (Finish (Either.Right workspace))) ->
    Just $ ExploreMode workspace (Just key) Nothing []

updateInputStringSlot :: Either String ModifiedKey -> (String, Int) -> InputResult (String, Int) String
updateInputStringSlot key (input, pos) = case key of
  Either.Right (ModifiedKey False False False Enter) ->
    Finish input
  Either.Right (ModifiedKey False False False Esc) ->
    Cancel
  Either.Right (ModifiedKey False False False (Char ch)) ->
    Wait [] (take pos input ++ [ch] ++ drop pos input, pos + 1)
  Either.Right (ModifiedKey False False False Backspace) ->
    Wait [] (take (pos - 1) input ++ drop pos input, max (pos - 1) 0)
  Either.Right (ModifiedKey False False False Delete) ->
    let
      input' = take pos input ++ drop (pos + 1) input
      pos' = min pos (length input')
    in
      Wait [] (input', pos')
  Either.Right (ModifiedKey False False False Left) ->
    Wait [] (input, max (pos - 1) 0)
  Either.Right (ModifiedKey False False False Right) ->
    Wait [] (input, min (pos + 1) (length input))
  _ -> Wait ["invalid input"] (input, pos)

updateInputState :: Either String ModifiedKey -> InputState a -> InputResult (InputState a) a
updateInputState key (InputStringState f input pos) = case updateInputStringSlot key (input, pos) of
  Cancel -> Cancel
  Wait messages (input, pos) -> Wait messages $ InputStringState f input pos
  Finish input -> Finish $ f input
updateInputState key state@(InputSelectionState f options index) = case key of
  Either.Right (ModifiedKey False False False Enter) ->
    Finish $ f (options !! index)
  Either.Right (ModifiedKey False False False Esc) ->
    Cancel
  Either.Right (ModifiedKey False False False Up) ->
    Wait [] $ InputSelectionState f options (max (index - 1) 0)
  Either.Right (ModifiedKey False False False Down) ->
    Wait [] $ InputSelectionState f options (min (index + 1) (length options - 1))
  _ -> Wait ["invalid input"] state
updateInputState key state@(InputPartitionState f partition index) = case key of
  Either.Right (ModifiedKey False False False Enter) ->
    Finish $ f partition
  Either.Right (ModifiedKey False False False Esc) ->
    Cancel
  Either.Right (ModifiedKey False False False Up) ->
    Wait [] $ InputPartitionState f partition (max (index - 1) 0)
  Either.Right (ModifiedKey False False False Down) ->
    Wait [] $ InputPartitionState f partition (min (index + 1) (length partition - 1))
  Either.Right (ModifiedKey True False False Up) ->
    let
      separator = partition |> fmap length |> scanl (+) 0
      group_index = separator |> findIndex (> index) |> fromJust |> (\i -> i - 1)
      group_offset = index - separator !! group_index
      extended_partition = [] : partition
      group_from = extended_partition !! (group_index + 1)
      group_to = extended_partition !! group_index
      group_from' = splice group_offset (group_offset + 1) [] group_from
      group_to' = group_from ++ [group_from !! group_offset]
      extended_partition' = splice group_index (group_index + 1) [group_to', group_from'] extended_partition
      index' = rangeTo (group_index + 1) extended_partition' |> fmap length |> sum |> (\i -> i - 1)
      partition' = extended_partition' |> filter notNull
    in
      Wait [] $ InputPartitionState f partition' index'
  Either.Right (ModifiedKey True False False Down) ->
    let
      separator = partition |> fmap length |> scanl (+) 0
      group_index = separator |> findIndex (> index) |> fromJust |> (\i -> i - 1)
      group_offset = index - separator !! group_index
      extended_partition = partition ++ [[]]
      group_from = extended_partition !! group_index
      group_to = extended_partition !! (group_index + 1)
      group_from' = splice group_offset (group_offset + 1) [] group_from
      group_to' = (group_from !! group_offset) : group_from
      extended_partition' = splice group_index (group_index + 1) [group_from', group_to'] extended_partition
      index' = rangeTo (group_index + 1) extended_partition' |> fmap length |> sum
      partition' = extended_partition' |> filter notNull
    in
      Wait [] $ InputPartitionState f partition' index'
  _ -> Wait ["invalid input"] state


run :: Either String ModifiedKey -> Editor -> IO (Maybe Editor)
run key editor = case update key editor of
  Nothing -> return Nothing
  Just next_editor -> do
    renderEditor next_editor
    return $ Just next_editor

edit :: String -> String -> IO ()
edit bac_path strs_path = do
  state <- initialize bac_path strs_path
  interact run state
