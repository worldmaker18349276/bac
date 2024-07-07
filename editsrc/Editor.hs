{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Editor where

import Control.Applicative (Alternative)
import Control.Exception (IOException, catch)
import Control.Monad (MonadPlus, when)
import Control.Monad.Trans.Maybe (MaybeT (MaybeT, runMaybeT))
import Control.Monad.Trans.Reader (ReaderT (ReaderT, runReaderT))
import qualified Data.Either as Either
import Data.Either.Extra (maybeToEither)
import Data.Foldable (find, forM_)
import Data.Function ((&))
import Data.List (findIndex, intersperse)
import Data.List.Extra (enumerate, notNull, nubSort, split)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, fromMaybe, isNothing, listToMaybe, mapMaybe)
import GHC.Base (Alternative (..))
import System.Environment (getArgs)
import Prelude hiding (Left, Right, interact)

import qualified BAC.Base as BAC
import BAC.Deserialize (deserializeWithValue)
import BAC.Prefix (Chain)
import qualified BAC.Prefix as Prefix
import Interactive (Key (..), KeyboardInput (..), interact)
import Workspace (Action (..), Cursor (..), Workspace (..), getBuffer, runAction, slotLength, Control (..), input, Slot)
import Utils

toAction :: KeyboardInput -> Maybe Action
toAction (ModifiedKey False False False Up)    = Just MoveUp
toAction (ModifiedKey False False False Down)  = Just MoveDown
toAction (ModifiedKey False False False Left)  = Just MoveLeft
toAction (ModifiedKey False False False Right) = Just MoveRight
toAction (ModifiedKey False False True  Left)  = Just MoveHome    -- Ctrl-Left
toAction (ModifiedKey False False True  Right) = Just MoveEnd     -- Ctrl-Right
toAction (ModifiedKey False True  False Up)    = Just DragUp      -- Alt-Up
toAction (ModifiedKey False True  False Down)  = Just DragDown    -- Alt-Down
toAction (ModifiedKey True  False False Up)    = Just SelectUp    -- Shift-Up
toAction (ModifiedKey True  False False Down)  = Just SelectDown  -- Shift-Down
toAction (ModifiedKey True  False False Left)  = Just SelectLeft  -- Shift-Left
toAction (ModifiedKey True  False False Right) = Just SelectRight -- Shift-Right
toAction (ModifiedKey True  False True  Left)  = Just SelectHome  -- Shift-Ctrl-Left
toAction (ModifiedKey True  False True  Right) = Just SelectEnd   -- Shift-Ctrl-Right
toAction (ModifiedKey False False False Tab)   = Just Search
toAction (ModifiedKey False False False Enter) = Just NewSlot
toAction (ModifiedKey False True  False Enter) = Just ChangeType
toAction (ModifiedKey False True  False Left)  = Just SwingLeft  -- Alt-Left
toAction (ModifiedKey False True  False Right) = Just SwingRight -- Alt-Right
toAction (ModifiedKey False False False Backspace) = Just DeleteBackward
toAction (ModifiedKey False True  False Backspace) = Just DeleteSlot -- Alt-Backspace
toAction (ModifiedKey False True  False (Char 'd')) = Just Dup -- Alt-'d'
toAction (ModifiedKey False True  False (Char 'j')) = Just Join -- Alt-'j'
toAction (ModifiedKey False True  False (Char 'i')) = Just InitialChain -- Alt-'i'
toAction _ = Nothing

data Status =
  Status {
    getKey :: Maybe KeyboardInput,
    getAction :: Maybe Action,
    getMessages :: [String]
  }

data Editor =
    ExploreMode {
      getWorkspace :: Workspace,
      getStatus :: Status
    }
  | CommandMode {
      getWorkspace :: Workspace,
      getInput :: (String, Int),
      getStatus :: Status
    }
  | InputMode {
      getWorkspace :: Workspace,
      getCurrentAction :: Action,
      getInputState :: InputStateRec (Either [String] Workspace),
      getStatus :: Status
    }

data InputState a where
  InputStringState :: String -> (String -> a) -> String -> Int -> InputState a
  InputSelectionState :: Show b => String -> (b -> a) -> [b] -> Int -> InputState a
  InputPartitionState :: Show b => String -> ([[b]] -> a) -> [[b]] -> Int -> InputState a

instance Functor InputState where
  fmap :: (a -> b) -> InputState a -> InputState b
  fmap callback' (InputStringState hint callback val i) = InputStringState hint (callback .> callback') val i
  fmap callback' (InputSelectionState hint callback val i) = InputSelectionState hint (callback .> callback') val i
  fmap callback' (InputPartitionState hint callback val i) = InputPartitionState hint (callback .> callback') val i

createInputStringState :: String -> (String -> a) -> InputState a
createInputStringState hint callback = InputStringState hint callback "" 0

createInputSelectionState :: Show b => String -> (b -> a) -> [b] -> InputState a
createInputSelectionState hint callback options = InputSelectionState hint callback options 0

createInputPartitionState :: Show b => String -> ([[b]] -> a) -> [b] -> InputState a
createInputPartitionState hint callback partition = InputPartitionState hint callback (fmap (: []) partition) 0

data InputStore a where
  InputStringStore :: (String -> a) -> String -> InputStore a
  InputSelectionStore :: (b -> a) -> b -> InputStore a
  InputPartitionStore :: ([[b]] -> a) -> [[b]] -> InputStore a

instance Functor InputStore where
  fmap :: (a -> b) -> InputStore a -> InputStore b
  fmap callback' (InputStringStore callback val) = InputStringStore (callback .> callback') val
  fmap callback' (InputSelectionStore callback val) = InputSelectionStore (callback .> callback') val
  fmap callback' (InputPartitionStore callback val) = InputPartitionStore (callback .> callback') val

extractInput :: InputState a -> InputStore a
extractInput (InputStringState _ callback val _) = InputStringStore callback val
extractInput (InputSelectionState _ callback options i) = InputSelectionStore callback (options !! i)
extractInput (InputPartitionState _ callback partition _) = InputPartitionStore callback partition

runCallback :: InputStore a -> a
runCallback (InputStringStore callback val) = callback val
runCallback (InputSelectionStore callback option) = callback option
runCallback (InputPartitionStore callback partition) = callback partition


data InputResult s r = Cancel | Finish r | NextStep [String] s deriving (Functor)

-- free MonadPlus of InputState
newtype InputControl r = InputControl (InputResult (InputState (InputControl r)) r)

-- = InputState (InputResult (..) r)
type InputStateRec r = InputState (InputControl r)

joinInputControl :: InputControl (InputControl a) -> InputControl a
joinInputControl (InputControl Cancel) = InputControl Cancel
joinInputControl (InputControl (Finish ctrl)) = ctrl
joinInputControl (InputControl (NextStep messages state)) =
  InputControl $ NextStep messages $ fmap joinInputControl state

instance Functor InputControl where
  fmap :: (a -> b) -> InputControl a -> InputControl b
  fmap f (InputControl Cancel) = InputControl Cancel
  fmap f (InputControl (Finish a)) = InputControl $ Finish (f a)
  fmap f (InputControl (NextStep messages state)) =
    InputControl $ NextStep messages $ fmap (fmap f) state

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
  inputString hint = InputControl $ NextStep [] $ createInputStringState hint return
  inputSelection :: Show a => String -> [a] -> InputControl a
  inputSelection hint options = InputControl $ NextStep [] $ createInputSelectionState hint return options
  inputPartition :: Show a => String -> [a] -> InputControl [[a]]
  inputPartition hint partition = InputControl $ NextStep [] $ createInputPartitionState hint return partition


renderSlot :: Maybe (Int, Int) -> Slot -> IO ()
renderSlot range (Either.Left str) = do
  let (l, h) = case range of
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
  buffer !! line cursor |> \case
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
        tokens |> take (column cursor) |> concat |> length |> (+ prelength)

renderWorkspace :: Workspace -> IO (Int, Int, Int)
renderWorkspace state@(Workspace { buffer, cursor }) = do
  forM_ (buffer `zip` [0..]) \(slot, i) -> renderSlot (getSubSelection state i) slot
  return (line cursor, getCursorColumn state, length buffer)


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
  forM_ (fmap ("! " ++) messages) putStrLn
  return $ length messages + 1

renderInputState :: Action -> InputState a -> IO (Int, Int, Int)
renderInputState action (InputStringState hint _ input pos) = do
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  putStrLn $ input ++ " "
  return (1, pos, 2)
renderInputState action (InputSelectionState hint _ options index) = do
  let strs =
        options
        |> fmap show
        |> zip [0..]
        |> fmap \(i, str) -> if i /= index then str else "\ESC[2m\ESC[7m" ++ str ++ "\ESC[27m\ESC[22m"
  putStrLn $ "[" ++ show action ++ "] " ++ hint
  forM_ strs putStrLn
  return (index + 1, 0, length options + 1)
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
  forM_ (getMessages status |> fmap ("! " ++)) putStrLn
  moveCursor (length (buffer state) + 1, pos + 2)
renderEditor (InputMode state inputState curr_action status) = do
  clear
  (_, _, lines) <- renderWorkspace state
  putStrLn "───────────────────────────────────"
  (ln, col, _) <- renderInputState inputState curr_action
  putStrLn "───────────────────────────────────"
  _ <- renderStatus status
  moveCursor (lines + 1 + ln, col)


update :: KeyboardInput -> Editor -> Maybe Editor

update key editor@(ExploreMode {}) =
  case toAction key of
    Nothing -> case key of
      ModifiedKey False False False Esc ->
        Just $ CommandMode (getWorkspace editor) ("", 0) (Status (Just key) Nothing [])
      ModifiedKey False False False (Char ch) ->
        case input [ch] (getWorkspace editor) of
          Either.Left messages ->
            Just $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing messages
          Either.Right workspace ->
            Just $ ExploreMode workspace $ Status (Just key) Nothing []
      _ ->
        Just $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing []
    Just action -> do
      case runAction action (getWorkspace editor) of
        InputControl Cancel ->
          Just $ ExploreMode (getWorkspace editor) $ Status (Just key) (Just action) ["cancelled"]
        InputControl (Finish (Either.Left messages)) ->
          Just $ ExploreMode (getWorkspace editor) $ Status (Just key) (Just action) messages
        InputControl (Finish (Either.Right next_state)) ->
          Just $ ExploreMode next_state $ Status (Just key) (Just action) []
        InputControl (NextStep messages state) ->
          Just $ InputMode (getWorkspace editor) action state $ Status (Just key) (Just action) messages

update key editor@(CommandMode {}) =
  case updateInputStringSlot (fmap show (enumerate :: [Action])) key (getInput editor) of
    Cancel ->
      Just $ ExploreMode (getWorkspace editor) $ Status Nothing Nothing []
    NextStep messages input ->
      Just $ CommandMode (getWorkspace editor) input $ Status Nothing Nothing messages
    Finish input -> case find (show .> (== input)) (enumerate :: [Action]) of
      Nothing ->
        Just $
          CommandMode (getWorkspace editor) (getInput editor) $
            Status Nothing Nothing ["unknown command: " ++ fst (getInput editor)]
      Just action -> do
        case runAction action (getWorkspace editor) of
          InputControl Cancel ->
            Just $ ExploreMode (getWorkspace editor) $ Status Nothing (Just action) ["cancelled"]
          InputControl (Finish (Either.Left messages)) ->
            Just $ ExploreMode (getWorkspace editor) $ Status Nothing (Just action) messages
          InputControl (Finish (Either.Right next_state)) ->
            Just $ ExploreMode next_state $ Status Nothing (Just action) []
          InputControl (NextStep messages state) ->
            Just $ InputMode (getWorkspace editor) action state $ Status Nothing (Just action) messages

update key editor@(InputMode {}) =
  case updateInputState key (getInputState editor) of
    Cancel ->
      Just $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing ["cancel action"]
    NextStep messages state ->
      Just $ InputMode (getWorkspace editor) (getCurrentAction editor) state $
        Status (Just key) Nothing messages
    Finish store -> case runCallback store of
      InputControl Cancel ->
        Just $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing ["cancelled"]
      InputControl (NextStep messages state) ->
        Just $ InputMode (getWorkspace editor) (getCurrentAction editor) state $
          Status (Just key) Nothing messages
      InputControl (Finish (Either.Left messages)) ->
        Just $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing messages
      InputControl (Finish (Either.Right workspace)) ->
        Just $ ExploreMode workspace $ Status (Just key) Nothing []

updateInputStringSlot :: [String] -> KeyboardInput -> (String, Int) -> InputResult (String, Int) String
updateInputStringSlot suggestions key (input, pos) = case key of
  ModifiedKey False False False Enter ->
    Finish input
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False (Char ch) ->
    NextStep [] (splice pos pos [ch] input, pos + 1)
  ModifiedKey False False False Tab ->
    let
      prefix = rangeTo pos input
      suffix = rangeFrom pos input
      suffixes = (input : suggestions) |> mapMaybe (`Prefix.strip` prefix) |> nubSort
      suffix' = suffixes |> find (> suffix) |> fromMaybe (head suffixes)
      messages = ["no suggestion" | length suffixes == 1]
    in
      NextStep messages (prefix ++ suffix', pos)
  ModifiedKey True False False Tab ->
    let
      prefix = rangeTo pos input
      suffix = rangeFrom pos input
      suffixes = (input : suggestions) |> mapMaybe (`Prefix.strip` prefix) |> nubSort
      suffix' = suffixes |> reverse |> find (< suffix) |> fromMaybe (last suffixes)
      messages = ["no suggestion" | length suffixes == 1]
    in
      NextStep messages (prefix ++ suffix', pos)
  ModifiedKey False False False Backspace ->
    NextStep [] (take (pos - 1) input ++ drop pos input, max (pos - 1) 0)
  ModifiedKey False False False Delete ->
    let
      input' = take pos input ++ drop (pos + 1) input
      pos' = min pos (length input')
    in
      NextStep [] (input', pos')
  ModifiedKey False False False Left ->
    NextStep [] (input, max (pos - 1) 0)
  ModifiedKey False False False Right ->
    NextStep [] (input, min (pos + 1) (length input))
  _ -> NextStep ["invalid input"] (input, pos)

updateInputState :: KeyboardInput -> InputState a -> InputResult (InputState a) (InputStore a)
updateInputState key state@(InputStringState hint f input pos) =
  case updateInputStringSlot [] key (input, pos) of
    Cancel -> Cancel
    NextStep messages (input, pos) -> NextStep messages $ InputStringState hint f input pos
    Finish input' -> Finish $ extractInput $ InputStringState hint f input' pos
updateInputState key state@(InputSelectionState hint f options index) = case key of
  ModifiedKey False False False Enter ->
    Finish $ extractInput state
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False Up ->
    NextStep [] $ InputSelectionState hint f options (max (index - 1) 0)
  ModifiedKey False False False Down ->
    NextStep [] $ InputSelectionState hint f options (min (index + 1) (length options - 1))
  _ -> NextStep ["invalid input"] state
updateInputState key state@(InputPartitionState hint f partition index) = case key of
  ModifiedKey False False False Enter ->
    Finish $ extractInput state
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False Up ->
    NextStep [] $ InputPartitionState hint f partition (max (index - 1) 0)
  ModifiedKey False False False Down ->
    NextStep [] $ InputPartitionState hint f partition (min (index + 1) (length partition - 1))
  ModifiedKey True False False Up ->
    let
      separator = partition |> fmap length |> scanl (+) 0
      group_index = separator |> findIndex (> index) |> fromJust |> (\i -> i - 1)
      group_offset = index - separator !! group_index
      extended_partition = [] : partition
      group_from = extended_partition !! (group_index + 1)
      group_to = extended_partition !! group_index
      group_from' = splice group_offset (group_offset + 1) [] group_from
      group_to' = group_to ++ [group_from !! group_offset]
      extended_partition' = splice group_index (group_index + 2) [group_to', group_from'] extended_partition
      index' = rangeTo (group_index + 1) extended_partition' |> fmap length |> sum |> (\i -> i - 1)
      partition' = extended_partition' |> filter notNull
    in
      NextStep [] $ InputPartitionState hint f partition' index'
  ModifiedKey True False False Down ->
    let
      separator = partition |> fmap length |> scanl (+) 0
      group_index = separator |> findIndex (> index) |> fromJust |> (\i -> i - 1)
      group_offset = index - separator !! group_index
      extended_partition = partition ++ [[]]
      group_from = extended_partition !! group_index
      group_to = extended_partition !! (group_index + 1)
      group_from' = splice group_offset (group_offset + 1) [] group_from
      group_to' = (group_from !! group_offset) : group_to
      extended_partition' = splice group_index (group_index + 2) [group_from', group_to'] extended_partition
      index' = rangeTo (group_index + 1) extended_partition' |> fmap length |> sum
      partition' = extended_partition' |> filter notNull
    in
      NextStep [] $ InputPartitionState hint f partition' index'
  _ -> NextStep ["invalid input"] state


safeReadFile :: String -> IO (Either [String] String)
safeReadFile path =
  (Either.Right <$> readFile path) `catch` \(e :: IOException) -> do
    return $ Either.Left ["fail to read file: " ++ path | notNull path]

initialize :: String -> String -> IO Editor
initialize bac_path strs_path = do
  let messages = ([] :: [String])

  (bac_contents, messages) <- safeReadFile bac_path
    |> fmap (either
      (\msgs -> ("", messages ++ msgs))
      (, messages))
  (strs_contents, messages) <- safeReadFile strs_path
    |> fmap (either
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
        |> split (== '\n')
        |> fmap \str -> str |> Prefix.fromString prefix_bac |> maybeToEither str
  let state = Workspace { bac = prefix_bac, buffer, cursor = Cursor 0 0 0 0 }

  let editor = ExploreMode state (Status Nothing Nothing messages)
  renderEditor editor
  return editor

run :: KeyboardInput -> Editor -> IO (Maybe Editor)
run key editor = case update key editor of
  Nothing -> return Nothing
  Just next_editor -> do
    renderEditor next_editor
    return $ Just next_editor

edit :: String -> String -> IO ()
edit bac_path strs_path = do
  state <- initialize bac_path strs_path
  interact run state
