{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}

module Editor where

import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import qualified Data.Either as Either
import Data.Foldable (find)
import Data.List (findIndex)
import Data.List.Extra (enumerate, notNull, nubSort)
import Data.Maybe (fromJust, fromMaybe, mapMaybe)
import Prelude hiding (Left, Right)

import qualified BAC.Prefix as Prefix
import Interactive (Key (..), KeyboardInput (..))
import Utils
import Workspace
  ( FileAccessControl (..),
    InputControl (..),
    Workspace,
    WorkspaceAction (..),
    emptyWorkspace,
    input,
    readBAC,
    readBank,
    runWorkspaceAction,
  )


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
      getOperationState :: SeriesOperationInputState ([String], Workspace),
      getStatus :: Status
    }

emtpyEditor :: Editor
emtpyEditor = ExploreMode emptyWorkspace $ Status Nothing Nothing []

openEditor :: FileAccessControl m => Maybe FilePath -> Maybe FilePath -> m Editor
openEditor bac_filepath bank_filepath = do
  let editor = emtpyEditor

  res <- case bac_filepath of
    Just filepath -> runExceptT $ readBAC filepath (getWorkspace editor)
    Nothing -> return $ return $ getWorkspace editor
  let editor' = case res of
        Either.Left messages ->
          ExploreMode (getWorkspace editor) $
            Status Nothing Nothing (getMessages (getStatus editor) ++ messages)
        Either.Right workspace' ->
          ExploreMode workspace' $
            Status Nothing Nothing (getMessages (getStatus editor))

  res <- case bank_filepath of
    Just filepath -> runExceptT $ readBank filepath (getWorkspace editor')
    Nothing -> return $ return $ getWorkspace editor'
  let editor'' = case res of
        Either.Left messages ->
          ExploreMode (getWorkspace editor') $
            Status Nothing Nothing (getMessages (getStatus editor') ++ messages)
        Either.Right workspace' ->
          ExploreMode workspace' $
            Status Nothing Nothing (getMessages (getStatus editor'))

  return editor''

data Action =
    WorkspaceAction WorkspaceAction
  | EditorEscape
  | EditorInput String

instance Show Action where
  show :: Action -> String
  show (WorkspaceAction action) = show action
  show EditorEscape = "Escape"
  show (EditorInput str) = show str

actions :: [(String, Action)]
actions =
  fmap (\a -> (show a, WorkspaceAction a)) workspace_actions
  ++ fmap (\a -> (show a, a)) other_actions
  where
  workspace_actions = enumerate :: [WorkspaceAction]
  other_actions = [EditorEscape]

toAction :: KeyboardInput -> Maybe Action
toAction (ModifiedKey False False False Esc) = Just EditorEscape
toAction (ModifiedKey False False False Up)    = Just $ WorkspaceAction MoveUp
toAction (ModifiedKey False False False Down)  = Just $ WorkspaceAction MoveDown
toAction (ModifiedKey False False False Left)  = Just $ WorkspaceAction MoveLeft
toAction (ModifiedKey False False False Right) = Just $ WorkspaceAction MoveRight
toAction (ModifiedKey False False True  Left)  = Just $ WorkspaceAction MoveHome    -- Ctrl-Left
toAction (ModifiedKey False False True  Right) = Just $ WorkspaceAction MoveEnd     -- Ctrl-Right
toAction (ModifiedKey False True  False Up)    = Just $ WorkspaceAction DragUp      -- Alt-Up
toAction (ModifiedKey False True  False Down)  = Just $ WorkspaceAction DragDown    -- Alt-Down
toAction (ModifiedKey True  False False Up)    = Just $ WorkspaceAction SelectUp    -- Shift-Up
toAction (ModifiedKey True  False False Down)  = Just $ WorkspaceAction SelectDown  -- Shift-Down
toAction (ModifiedKey True  False False Left)  = Just $ WorkspaceAction SelectLeft  -- Shift-Left
toAction (ModifiedKey True  False False Right) = Just $ WorkspaceAction SelectRight -- Shift-Right
toAction (ModifiedKey True  False True  Left)  = Just $ WorkspaceAction SelectHome  -- Shift-Ctrl-Left
toAction (ModifiedKey True  False True  Right) = Just $ WorkspaceAction SelectEnd   -- Shift-Ctrl-Right
toAction (ModifiedKey False False False Tab)   = Just $ WorkspaceAction Search
toAction (ModifiedKey False False False Enter) = Just $ WorkspaceAction NewSlot
toAction (ModifiedKey False True  False Enter) = Just $ WorkspaceAction ChangeType
toAction (ModifiedKey False True  False Left)  = Just $ WorkspaceAction SwingLeft  -- Alt-Left
toAction (ModifiedKey False True  False Right) = Just $ WorkspaceAction SwingRight -- Alt-Right
toAction (ModifiedKey False False False Backspace)  = Just $ WorkspaceAction DeleteBackward
toAction (ModifiedKey False True  False Backspace)  = Just $ WorkspaceAction DeleteSlot -- Alt-Backspace
toAction (ModifiedKey False True  False (Char 'd')) = Just $ WorkspaceAction Dup -- Alt-'d'
toAction (ModifiedKey False True  False (Char 'j')) = Just $ WorkspaceAction Join -- Alt-'j'
toAction (ModifiedKey False True  False (Char 'i')) = Just $ WorkspaceAction InitialChain -- Alt-'i'
toAction (ModifiedKey False False False (Char ch))  = Just $ EditorInput [ch]
toAction (ModifiedKey False True  False (Char 's')) = Just $ WorkspaceAction SaveAll -- Alt-'s'
toAction (ModifiedKey False True  False (Char 'S')) = Just $ WorkspaceAction SaveBankAs -- Alt-Shift-'s'
toAction (ModifiedKey False True  False (Char 'o')) = Just $ WorkspaceAction OpenBankFrom -- Alt-'o'
toAction (ModifiedKey False True  False (Char 'O')) = Just $ WorkspaceAction AppendBankFrom -- Alt-'O'
toAction _ = Nothing


data InputState a where
  InputStringState :: String -> (Either [String] String -> a) -> String -> Int -> InputState a
  InputSelectionState :: Show b => String -> (Either [String] b -> a) -> [b] -> Int -> InputState a
  InputPartitionState :: Show b => String -> (Either [String] [[b]] -> a) -> [[b]] -> Int -> InputState a

instance Functor InputState where
  fmap :: (a -> b) -> InputState a -> InputState b
  fmap callback' (InputStringState hint callback val i) = InputStringState hint (callback .> callback') val i
  fmap callback' (InputSelectionState hint callback val i) = InputSelectionState hint (callback .> callback') val i
  fmap callback' (InputPartitionState hint callback val i) = InputPartitionState hint (callback .> callback') val i

data FileAccessState a =
    FileSaveState (Either [String] () -> a) String FilePath
  | FileOpenState (Either [String] String -> a) FilePath
  deriving (Functor)


-- free Monad of InputState + FileAccessState
data SeriesOperationState r =
    SeriesOperationFinish r
  | NextInput (InputState (SeriesOperationState r))
  | NextFileAccess (FileAccessState (SeriesOperationState r))
  deriving (Functor)

type SeriesOperationInputState r = InputState (SeriesOperationState r)
type SeriesOperationFileAccessState r = FileAccessState (SeriesOperationState r)

joinSeriesOperationState :: SeriesOperationState (SeriesOperationState a) -> SeriesOperationState a
joinSeriesOperationState (SeriesOperationFinish ctrl) = ctrl
joinSeriesOperationState (NextInput state) =
  NextInput $ fmap joinSeriesOperationState state
joinSeriesOperationState (NextFileAccess state) =
  NextFileAccess $ fmap joinSeriesOperationState state

instance Applicative SeriesOperationState where
  pure :: a -> SeriesOperationState a
  pure = SeriesOperationFinish
  (<*>) :: SeriesOperationState (a -> b) -> SeriesOperationState a -> SeriesOperationState b
  mf <*> ma = mf >>= (`fmap` ma)

instance Monad SeriesOperationState where
  (>>=) :: SeriesOperationState a -> (a -> SeriesOperationState b) -> SeriesOperationState b
  state >>= f = fmap f state |> joinSeriesOperationState

instance InputControl SeriesOperationState where
  inputString :: String -> ExceptT [String] SeriesOperationState String
  inputString hint =
    ExceptT $ NextInput $ InputStringState hint return "" 0
  inputSelection :: Show a => String -> [a] -> ExceptT [String] SeriesOperationState a
  inputSelection hint [] =
    ExceptT $ SeriesOperationFinish $ Either.Left ["no item to select"]
  inputSelection hint options =
    ExceptT $ NextInput $ InputSelectionState hint return options 0
  inputPartition :: Show a => String -> [a] -> ExceptT [String] SeriesOperationState [[a]]
  inputPartition hint [] =
    ExceptT $ SeriesOperationFinish $ Either.Left ["no item to partition"]
  inputPartition hint partition =
    ExceptT $ NextInput $ InputPartitionState hint return (fmap (: []) partition) 0

instance FileAccessControl SeriesOperationState where
  save :: FilePath -> String -> ExceptT [String] SeriesOperationState ()
  save filepath contents = ExceptT $ NextFileAccess $ FileSaveState return contents filepath
  open :: FilePath -> ExceptT [String] SeriesOperationState String
  open filepath = ExceptT $ NextFileAccess $ FileOpenState return filepath

extractInput :: InputState a -> a
extractInput (InputStringState _ callback val _) = callback (Either.Right val)
extractInput (InputSelectionState _ callback options i) = callback (Either.Right $ options !! i)
extractInput (InputPartitionState _ callback partition _) = callback (Either.Right partition)

failInput :: [String] -> InputState a -> a
failInput msgs (InputStringState _ callback _ _) = callback (Either.Left msgs)
failInput msgs (InputSelectionState _ callback _ _) = callback (Either.Left msgs)
failInput msgs (InputPartitionState _ callback _ _) = callback (Either.Left msgs)


update :: FileAccessControl m => KeyboardInput -> Editor -> m Editor
update key editor@(ExploreMode {}) =
  case toAction key of
    Nothing -> return $ ExploreMode (getWorkspace editor) $ Status (Just key) Nothing []
    Just action -> runAction (Just key) action editor
update key editor@(CommandMode {}) =
  case updateInputStringSlot (fmap fst actions) key (getInput editor) of
    Cancel ->
      return $ ExploreMode (getWorkspace editor) $ Status Nothing Nothing []
    Continue messages input ->
      return $ CommandMode (getWorkspace editor) input $ Status Nothing Nothing messages
    Finish input -> case find (fst .> (== input)) actions of
      Nothing ->
        return $
          CommandMode (getWorkspace editor) (getInput editor) $
            Status Nothing Nothing ["unknown command: " ++ fst (getInput editor)]
      Just (_, action) ->
        runAction Nothing action editor
update key editor@(InputMode {}) =
  case updateInputState' key (getOperationState editor) of
    Continue messages state ->
      return $ InputMode (getWorkspace editor) (getCurrentAction editor) state $ Status (Just key) Nothing messages
    Finish (SeriesOperationFinish (messages, workspace')) ->
      return $ ExploreMode workspace' $ Status (Just key) Nothing messages
    Finish (NextInput state) ->
      return $ InputMode (getWorkspace editor) (getCurrentAction editor) state $ Status (Just key) Nothing []
    Finish (NextFileAccess state) -> do
      res <- updateFileAccessState state
      case res of
        Either.Left state ->
          return $ InputMode (getWorkspace editor) (getCurrentAction editor) state $ Status (Just key) Nothing []
        Either.Right (messages, workspace') ->
          return $ ExploreMode workspace' $ Status (Just key) Nothing messages
    Cancel -> error "unreachable"

runAction :: FileAccessControl m => Maybe KeyboardInput -> Action -> Editor -> m Editor
runAction key EditorEscape editor =
  return $ CommandMode (getWorkspace editor) ("", 0) (Status key Nothing [])
runAction key (EditorInput str) editor =
  let (messages, workspace) = input str (getWorkspace editor)
  in return $ ExploreMode workspace $ Status key Nothing messages
runAction key action@(WorkspaceAction action') editor =
  case runWorkspaceAction action' (getWorkspace editor) of
    SeriesOperationFinish (messages, workspace') ->
      return $ ExploreMode workspace' $ Status key (Just action) messages
    NextInput state ->
      return $ InputMode (getWorkspace editor) action state $ Status key (Just action) []
    NextFileAccess state -> do
      res <- updateFileAccessState state
      case res of
        Either.Left state ->
          return $ InputMode (getWorkspace editor) action state $ Status key (Just action) []
        Either.Right (messages, workspace') ->
          return $ ExploreMode workspace' $ Status key (Just action) messages

updateFileAccessState ::
  FileAccessControl m
  => FileAccessState (SeriesOperationState r)
  -> m (Either (SeriesOperationInputState r) r)
updateFileAccessState state = do
  res <- case state of
    FileSaveState callback contents filepath ->
      save filepath contents |> runExceptT |> fmap callback
    FileOpenState callback filepath ->
      open filepath |> runExceptT |> fmap callback
  case res of
    SeriesOperationFinish r -> return $ Either.Right r
    NextInput state -> return $ Either.Left state
    NextFileAccess state -> updateFileAccessState state

data InputResult s r = Cancel | Finish r | Continue [String] s deriving (Functor)

updateInputStringSlot :: [String] -> KeyboardInput -> (String, Int) -> InputResult (String, Int) String
updateInputStringSlot suggestions key (input, pos) = case key of
  ModifiedKey False False False Enter ->
    Finish input
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False (Char ch) ->
    Continue [] (splice pos pos [ch] input, pos + 1)
  ModifiedKey False False False Tab ->
    let
      prefix = rangeTo pos input
      suffix = rangeFrom pos input
      suffixes = (input : suggestions) |> mapMaybe (`Prefix.strip` prefix) |> nubSort
      suffix' = suffixes |> find (> suffix) |> fromMaybe (head suffixes)
      messages = ["no suggestion" | length suffixes == 1]
    in
      Continue messages (prefix ++ suffix', pos)
  ModifiedKey True False False Tab ->
    let
      prefix = rangeTo pos input
      suffix = rangeFrom pos input
      suffixes = (input : suggestions) |> mapMaybe (`Prefix.strip` prefix) |> nubSort
      suffix' = suffixes |> reverse |> find (< suffix) |> fromMaybe (last suffixes)
      messages = ["no suggestion" | length suffixes == 1]
    in
      Continue messages (prefix ++ suffix', pos)
  ModifiedKey False False False Backspace ->
    Continue [] (take (pos - 1) input ++ drop pos input, max (pos - 1) 0)
  ModifiedKey False False False Delete ->
    let
      input' = take pos input ++ drop (pos + 1) input
      pos' = min pos (length input')
    in
      Continue [] (input', pos')
  ModifiedKey False False False Left ->
    Continue [] (input, max (pos - 1) 0)
  ModifiedKey False False False Right ->
    Continue [] (input, min (pos + 1) (length input))
  _ -> Continue ["invalid input"] (input, pos)

updateInputState' :: KeyboardInput -> InputState a -> InputResult (InputState a) a
updateInputState' key state =
  case updateInputState key state of
    Cancel -> Finish $ failInput ["cancel action"] state
    r -> r

updateInputState :: KeyboardInput -> InputState a -> InputResult (InputState a) a
updateInputState key state@(InputStringState hint f input pos) =
  case updateInputStringSlot [] key (input, pos) of
    Cancel -> Cancel
    Continue messages (input, pos) -> Continue messages $ InputStringState hint f input pos
    Finish input' -> Finish $ extractInput $ InputStringState hint f input' pos
updateInputState key state@(InputSelectionState hint f options index) = case key of
  ModifiedKey False False False Enter ->
    Finish $ extractInput state
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False Up ->
    Continue [] $ InputSelectionState hint f options (max 0 $ index - 1)
  ModifiedKey False False False Down ->
    Continue [] $ InputSelectionState hint f options (max 0 $ min (length options - 1) $ index + 1)
  _ -> Continue ["invalid input"] state
updateInputState key state@(InputPartitionState hint f partition index) = case key of
  ModifiedKey False False False Enter ->
    Finish $ extractInput state
  ModifiedKey False False False Esc ->
    Cancel
  ModifiedKey False False False Up ->
    Continue [] $ InputPartitionState hint f partition (max 0 $ index - 1)
  ModifiedKey False False False Down ->
    Continue [] $ InputPartitionState hint f partition (max 0 $ min (sum (fmap length partition) - 1) $ index + 1)
  ModifiedKey False True False Up ->
    if null partition then
      Continue [] $ InputPartitionState hint f partition 0
    else
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
        Continue [] $ InputPartitionState hint f partition' index'
  ModifiedKey False True False Down ->
    if null partition then
      Continue [] $ InputPartitionState hint f partition 0
    else
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
        Continue [] $ InputPartitionState hint f partition' index'
  _ -> Continue ["invalid input"] state
