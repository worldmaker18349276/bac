{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE TupleSections #-}

module Workspace where

import Control.Monad (guard, when, unless)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Data.Bifunctor (first)
import Data.Char (isPrint)
import Data.Either (isLeft, isRight)
import Data.Either.Extra (maybeToEither)
import Data.List (find, findIndex, intercalate)
import Data.List.Extra (notNull, split)
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe, maybeToList)
import Data.Tuple.Extra (both)

import BAC.Prefix (Chain, Node, PrefixBAC, PrefixOrdering (..), (==-), (===), (==~))
import qualified BAC
import qualified BAC.Prefix as Prefix
import Utils


showChain :: Chain -> String
showChain chain = "(" ++ Prefix.getPreString chain ++ ")" ++ concat (Prefix.getStrings chain)

data Cursor = Cursor { line :: Int, column :: Int, lineFrom :: Int, columnFrom :: Int }

type Slot = Either String Chain

data Workspace = Workspace {
  bac_filepath :: Maybe FilePath,
  bank_filepath :: Maybe FilePath,
  bac :: PrefixBAC,
  bank :: [Slot],
  cursor :: Cursor
}

emptyWorkspace :: Workspace
emptyWorkspace =
  Workspace {
    bac_filepath = Nothing,
    bank_filepath = Nothing,
    bac = Prefix.empty,
    bank = [Left ""],
    cursor = Cursor 0 0 0 0
  }

class Monad m => InputControl m where
  inputString :: String -> ExceptT [String] m String
  inputSelection :: Show a => String -> [a] -> ExceptT [String] m a
  inputPartition :: Show a => String -> [a] -> ExceptT [String] m [[a]]

class Monad m => FileAccessControl m where
  writeString :: FilePath -> String -> ExceptT [String] m ()
  readString :: FilePath -> ExceptT [String] m String

data WorkspaceAction =
    MoveUp
  | MoveDown
  | MoveLeft
  | MoveRight
  | MoveHome
  | MoveEnd
  | DragUp
  | DragDown
  | SelectUp
  | SelectDown
  | SelectLeft
  | SelectRight
  | SelectHome
  | SelectEnd
  | Dup
  | NewSlot
  | Join
  | DeleteBackward
  | DeleteSlot
  | ChangeType
  | InitialChain
  | IsNondecomposable
  | AreSameMorphism
  | AreUnsplittable
  | IsValidBAC
  | SwingLeft
  | SwingRight
  | DivideLeft
  | DivideRight
  | Search
  | AddEdge
  | RemoveEdge
  | AlterEdge
  | RemoveMorphism
  | RemoveObject
  | AddMorphism
  | AddObject
  | InterpolateObject
  | SplitMorphism
  | SplitObjectOutgoing
  | SplitObjectIncoming
  | MergeMorphisms
  | MergeObjectsOutgoing
  | MergeObjectsIncoming
  | GetFilePath
  | SaveAll
  | AskSaveAll
  | SaveBACAs
  | SaveBankAs
  | OpenBACFrom
  | OpenBankFrom
  | AppendBankFrom
  | ShowContents
  | RefineContents
  deriving (Show, Enum, Bounded)


runWorkspaceAction :: (InputControl m, FileAccessControl m) => WorkspaceAction -> Workspace -> m ([String], Workspace)
runWorkspaceAction MoveUp = moveUp .> return .> return
runWorkspaceAction MoveDown = moveDown .> return .> return
runWorkspaceAction MoveLeft = moveLeft .> return .> return
runWorkspaceAction MoveRight = moveRight .> return .> return
runWorkspaceAction MoveHome = moveHome .> return .> return
runWorkspaceAction MoveEnd = moveEnd .> return .> return
runWorkspaceAction DragUp = dragUp .> return .> return
runWorkspaceAction DragDown = dragDown .> return .> return
runWorkspaceAction SelectUp = selectUp .> return .> return
runWorkspaceAction SelectDown = selectDown .> return .> return
runWorkspaceAction SelectLeft = selectLeft .> return .> return
runWorkspaceAction SelectRight = selectRight .> return .> return
runWorkspaceAction SelectHome = selectHome .> return .> return
runWorkspaceAction SelectEnd = selectEnd .> return .> return
runWorkspaceAction Dup = dup .> return .> return
runWorkspaceAction NewSlot = newSlot .> return .> return
runWorkspaceAction Join = join .> return
runWorkspaceAction DeleteBackward = deleteBackward .> return
runWorkspaceAction DeleteSlot = deleteSlot .> return
runWorkspaceAction ChangeType = changeType .> return
runWorkspaceAction InitialChain = initialChain .> return
runWorkspaceAction IsNondecomposable = isNondecomposable .> return
runWorkspaceAction AreSameMorphism = areSameMorphism .> return
runWorkspaceAction AreUnsplittable = areUnsplittable .> return
runWorkspaceAction IsValidBAC = isValidBAC .> return
runWorkspaceAction SwingLeft = swingLeft .> return
runWorkspaceAction SwingRight = swingRight .> return
runWorkspaceAction DivideLeft = divideLeft .> return
runWorkspaceAction DivideRight = divideRight .> return
runWorkspaceAction Search = search .> return
runWorkspaceAction AddEdge = addEdge
runWorkspaceAction RemoveEdge = removeEdge
runWorkspaceAction AlterEdge = alterEdge
runWorkspaceAction RemoveMorphism = removeMorphism
runWorkspaceAction RemoveObject = removeObject
runWorkspaceAction AddMorphism = addMorphism
runWorkspaceAction AddObject = addObject
runWorkspaceAction InterpolateObject = interpolateObject
runWorkspaceAction SplitMorphism = splitMorphism
runWorkspaceAction SplitObjectOutgoing = splitObjectOutgoing
runWorkspaceAction SplitObjectIncoming = splitObjectIncoming
runWorkspaceAction MergeMorphisms = mergeMorphisms
runWorkspaceAction MergeObjectsOutgoing = mergeObjectsOutgoing
runWorkspaceAction MergeObjectsIncoming = mergeObjectsIncoming
runWorkspaceAction GetFilePath = getFilePath .> return
runWorkspaceAction SaveAll = saveAll
runWorkspaceAction AskSaveAll = askSaveAll
runWorkspaceAction SaveBACAs = saveBACAs
runWorkspaceAction SaveBankAs = saveBankAs
runWorkspaceAction OpenBACFrom = openBACFrom
runWorkspaceAction OpenBankFrom = openBankFrom
runWorkspaceAction AppendBankFrom = appendBankFrom
runWorkspaceAction ShowContents = showContents .> return
runWorkspaceAction RefineContents = refineContents .> return


cursorAt :: Int -> Int -> Cursor
cursorAt line column = Cursor line column line column

selectLines :: Workspace -> Int -> Int -> Cursor
selectLines workspace line_from line_to =
  if line_from <= line_to then
    Cursor line_to (slotLength (bank workspace !! line_to)) line_from 0
  else
    Cursor line_to 0 line_from (slotLength (bank workspace !! line_from))

slotLength :: Slot -> Int
slotLength (Left str) = length str
slotLength (Right chain) = Prefix.length chain

slotToString :: Slot -> String
slotToString (Left str) = str
slotToString (Right chain) = Prefix.getStrings chain |> concat

slotFromString :: PrefixBAC -> String -> Slot
slotFromString prefix_bac str = str |> Prefix.fromString prefix_bac |> maybeToEither str

getBankRange :: Workspace -> [Slot]
getBankRange (Workspace { cursor, bank }) =
  bank
  |> range
    (min (line cursor) (lineFrom cursor))
    (max (line cursor) (lineFrom cursor) + 1)

getCurrentSlot :: Workspace -> Slot
getCurrentSlot (Workspace { cursor, bank }) = bank !! line cursor

getCurrentSlotRange :: Workspace -> Maybe Slot
getCurrentSlotRange workspace@(Workspace { cursor })
  | line cursor /= lineFrom cursor = Nothing
  | otherwise = case getCurrentSlot workspace of
    Left str -> str |> range (min from to) (max from to) |> Left |> Just
    Right chain ->
      chain
      |> Prefix.split (max from to) |> fromJust |> fst
      |> Prefix.split (min from to) |> fromJust |> snd
      |> Right
      |> Just
  where
  from = columnFrom cursor
  to = column cursor

moveDown :: Workspace -> Workspace
moveDown workspace@(Workspace { cursor, bank })
  | line cursor < length bank - 1
  = workspace { cursor = cursorAt (line cursor + 1) 0 }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) 0 }

moveUp :: Workspace -> Workspace
moveUp workspace@(Workspace { cursor, bank })
  | line cursor > 0
  = workspace { cursor = cursorAt (line cursor - 1) 0 }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) 0 }

moveRight :: Workspace -> Workspace
moveRight workspace@(Workspace { cursor, bank })
  | column cursor < slotLength (bank !! line cursor)
  = workspace { cursor = cursorAt (line cursor) (column cursor + 1) }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) (column cursor) }

moveLeft :: Workspace -> Workspace
moveLeft workspace@(Workspace { cursor })
  | column cursor > 0
  = workspace { cursor = cursorAt (line cursor) (column cursor - 1) }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) (column cursor) }

moveEnd :: Workspace -> Workspace
moveEnd workspace@(Workspace { cursor, bank }) =
  workspace { cursor = cursorAt (line cursor) (slotLength (bank !! line cursor)) }

moveHome :: Workspace -> Workspace
moveHome workspace@(Workspace { cursor }) =
  workspace { cursor = cursorAt (line cursor) 0 }

dragDown :: Workspace -> Workspace
dragDown workspace@(Workspace { cursor, bank })
  | to < length bank
  = workspace {
      cursor = cursor { line = line cursor + 1, lineFrom = lineFrom cursor + 1 },
      bank = bank |> rangeTo from <> range to (to + 1) <> range from to <> rangeFrom (to + 1)
    }
  | otherwise
  = workspace
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1

dragUp :: Workspace -> Workspace
dragUp workspace@(Workspace { cursor, bank })
  | from > 0
  = workspace {
      cursor = cursor { line = line cursor - 1, lineFrom = lineFrom cursor - 1 },
      bank = bank |> rangeTo (from - 1) <> range from to <> range (from - 1) from <> rangeFrom to
    }
  | otherwise
  = workspace
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1

selectDown :: Workspace -> Workspace
selectDown workspace@(Workspace { cursor, bank })
  | line cursor < length bank - 1
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor + 1) }
  | otherwise
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor) }

selectUp :: Workspace -> Workspace
selectUp workspace@(Workspace { cursor, bank })
  | line cursor > 0
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor - 1) }
  | otherwise
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor) }

selectRight :: Workspace -> Workspace
selectRight workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor
  = workspace
  | column cursor < slotLength (bank !! line cursor)
  = workspace { cursor = cursor { column = column cursor + 1 } }
  | otherwise
  = workspace

selectLeft :: Workspace -> Workspace
selectLeft workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor
  = workspace
  | column cursor > 0
  = workspace { cursor = cursor { column = column cursor - 1 } }
  | otherwise
  = workspace

selectEnd :: Workspace -> Workspace
selectEnd workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor
  = workspace
  | otherwise
  = workspace { cursor = cursor { column = slotLength (bank !! line cursor) } }

selectHome :: Workspace -> Workspace
selectHome workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor
  = workspace
  | otherwise
  = workspace { cursor = cursor { column = 0 } }

dup :: Workspace -> Workspace
dup workspace@(Workspace { cursor, bank }) =
  workspace {
    bank = splice dup_line dup_line dup_slots bank,
    cursor = dup_cursor
  }
  where
  dup_slots =
    if line cursor == lineFrom cursor && column cursor == columnFrom cursor then
      [bank !! line cursor]
    else
      getCurrentSlotRange workspace |> maybe (getBankRange workspace) (: [])
  dup_line = max (line cursor) (lineFrom cursor) + 1
  shift_line = abs (line cursor - lineFrom cursor) + 1
  dup_cursor
    | line cursor == lineFrom cursor && column cursor > columnFrom cursor
    = Cursor (line cursor + shift_line) (slotLength (head dup_slots)) (lineFrom cursor + shift_line) 0
    | line cursor == lineFrom cursor && column cursor < columnFrom cursor
    = Cursor (line cursor + shift_line) 0 (lineFrom cursor + shift_line) (slotLength (head dup_slots))
    | otherwise
    = cursor { line = line cursor + shift_line, lineFrom = lineFrom cursor + shift_line }

newSlot :: Workspace -> Workspace
newSlot workspace@(Workspace { cursor, bank }) =
  workspace {
    bank = splice line' line' [Left ""] bank,
    cursor = cursorAt line' 0
  }
  where
  line' = max (line cursor) (lineFrom cursor) + 1

join :: Workspace -> ([String], Workspace)
join workspace@(Workspace { cursor, bank })
  | all isLeft bank'
  = return workspace {
      bank = splice from to [Left $ concatMap fromLeft bank'] bank,
      cursor = cursorAt from 0
    }
  | all isRight bank'
  = case foldl1M Prefix.join $ fmap fromRight bank' of
    Just join_chain ->
      return workspace {
        bank = splice from to [Right join_chain] bank,
        cursor = cursorAt from 0
      }
    Nothing -> (["cannot join those chains"], workspace)
  | otherwise
  = (["cannot join strings and chains"], workspace)
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  bank' = range from to bank

input :: String -> Workspace -> ([String], Workspace)
input str workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor || isRight (bank !! line cursor)
  = (["should on a string slot"], workspace)
  | not (all isPrint str)
  = (["cannot input non-printable character"], workspace)
  | otherwise
  = return workspace {
      bank =
        bank
        |> rangeTo (line cursor)
          <> const [Left $ splice from to str $ fromLeft (bank !! line cursor)]
          <> rangeFrom (line cursor + 1),
      cursor = cursorAt (line cursor) col
    }
  where
  from = min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
  col = from + length str

deleteBackward :: Workspace -> ([String], Workspace)
deleteBackward workspace@(Workspace { cursor, bank })
  | line cursor /= lineFrom cursor || slotLength (bank !! line cursor) == 0
  = let
      line' = min (line cursor) (lineFrom cursor) - 1
      cursor' = if line' < 0 then cursorAt 0 0 else cursorAt line' (slotLength (bank !! line'))
    in
      return workspace { bank = replace_slots [], cursor = cursor' }
  | otherwise
  = case bank !! line cursor of
    Left str ->
      return workspace {
        bank = replace_slots [Left $ splice from to "" str],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 && to == Prefix.length chain && column cursor < columnFrom cursor ->
      return workspace {
        bank = replace_slots [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 && to == Prefix.length chain && column cursor > columnFrom cursor ->
      return workspace {
        bank = replace_slots [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | to == Prefix.length chain ->
      return workspace {
        bank = replace_slots [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 ->
      return workspace {
        bank = replace_slots [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain ->
      (["can only delete end of chains"], workspace)
  where
  from =
    if column cursor == columnFrom cursor && column cursor /= 0 then
      column cursor - 1
    else
      min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
  replace_slots slots = if null bank' then [Left ""] else bank'
    where
    from = min (line cursor) (lineFrom cursor)
    to = max (line cursor) (lineFrom cursor) + 1
    bank' = splice from to slots bank

deleteSlot :: Workspace -> ([String], Workspace)
deleteSlot workspace@(Workspace { cursor, bank }) =
  return workspace { bank = replace_slots [], cursor = cursorAt line' 0 }
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  line' = max (from - 1) 0
  replace_slots slots = if null bank' then [Left ""] else bank'
    where
    from = min (line cursor) (lineFrom cursor)
    to = max (line cursor) (lineFrom cursor) + 1
    bank' = splice from to slots bank

changeType :: Workspace -> ([String], Workspace)
changeType workspace@(Workspace { bac, cursor, bank })
  | line cursor /= lineFrom cursor
  = (["should on a single slot"], workspace)
  | otherwise
  = case bank !! line cursor of
    Right chain ->
      return workspace {
        bank = replace_slots (Left $ concat $ Prefix.getStrings chain),
        cursor = cursorAt (line cursor) 0
      }
    Left str | null str ->
        return workspace {
          bank = replace_slots (Right $ Prefix.id $ Prefix.root bac),
          cursor = cursorAt (line cursor) 0
        }
    Left str -> case Prefix.fromString bac str of
      Nothing -> (["not a valid chain"], workspace)
      Just chain ->
        return workspace {
          bank = replace_slots (Right chain),
          cursor = cursorAt (line cursor) 0
        }
  where
  replace_slots slot = splice (line cursor) (line cursor + 1) [slot] bank

initialChain :: Workspace -> ([String], Workspace)
initialChain workspace@(Workspace { bac, cursor, bank })
  | line cursor /= lineFrom cursor || isLeft (bank !! line cursor) || slotLength (bank !! line cursor) /= 0
  = (["should be a node"], workspace)
  | otherwise
  = let
      pretoken = Prefix.getPreString $ fromRight $ bank !! line cursor
      init_chain =
        if null pretoken then
          Prefix.id (Prefix.root bac)
        else
          fromJust (Prefix.fromString bac pretoken)
    in return workspace {
        bank = splice (line cursor) (line cursor + 1) [Right init_chain] bank,
        cursor = cursorAt (line cursor) (Prefix.length init_chain)
      }

isNondecomposable :: Workspace -> ([String], Workspace)
isNondecomposable workspace@(Workspace { bac, cursor, bank })
  | line cursor /= lineFrom cursor || isLeft (bank !! line cursor)
  = (["should be a chain"], workspace)
  | otherwise
  = ([show $ Prefix.isNondecomposable $ fromRight $ bank !! line cursor], workspace)

areSameMorphism :: Workspace -> ([String], Workspace)
areSameMorphism workspace
  | not (all isRight $ getBankRange workspace)
  = (["should be chains"], workspace)
  | otherwise
  = ([getBankRange workspace |> fmap fromRight |> allSameBy (==~) |> show], workspace)

areUnsplittable :: Workspace -> ([String], Workspace)
areUnsplittable workspace
  | not (all isRight $ getBankRange workspace)
  = (["should be chains"], workspace)
  | otherwise
  = ([getBankRange workspace |> fmap fromRight |> allSameBy Prefix.isUnsplittable |> show], workspace)

isValidBAC :: Workspace -> ([String], Workspace)
isValidBAC workspace@(Workspace { bac }) = ([show (Prefix.validate bac)], workspace)

swingLeft :: Workspace -> ([String], Workspace)
swingLeft workspace@(Workspace { bac, cursor, bank })
  | line cursor /= lineFrom cursor || isLeft (bank !! line cursor)
  = (["should be a chain"], workspace)
  | column cursor == columnFrom cursor && column cursor == 0
  = case chain |> Prefix.source |> Prefix.incoming bac of
    edge : _ -> return workspace {
      bank = replace_slots (Right $ edge `join` chain),
      cursor = cursorAt (line cursor) 1
    }
    _ -> (["no edge to extend"], workspace)
  | column cursor == columnFrom cursor && column cursor == 1
  = let
      (edge, chain') = split 1 chain
      edges = chain' |> Prefix.source |> Prefix.incoming bac
      edge' = edges |> findIndex (=== edge) |> fromJust |> (+ 1) |> (`mod` length edges) |> (edges !!)
    in
      return workspace { bank = replace_slots (Right $ edge' `join` chain') }
  | column cursor == columnFrom cursor
  = (["should at the start position or with selection"], workspace)
  | otherwise
  = let
      from = min (column cursor) (columnFrom cursor)
      to = max (column cursor) (columnFrom cursor)
      ((chain1, chain2), chain3) = first (split from) $ split to chain
      (prefix, suffix) = split 1 chain2
      prefixes = Prefix.prefixes chain2
      (prefix', suffix') =
        prefixes |> findIndex (\(pref, suff) -> pref === prefix && suff ==~ suffix) |> fromJust
        |> (+ 1) |> (`mod` length prefixes) |> (prefixes !!)
      chain' = chain1 `join` prefix' `join` suffix' `join` chain3
      to' = Prefix.length chain' - Prefix.length chain3
      (col, colFrom) = if column cursor < columnFrom cursor then (from, to') else (to', from)
    in
      return workspace {
        bank = replace_slots (Right chain'),
        cursor = Cursor (line cursor) col (line cursor) colFrom
      }
  where
  chain = fromRight $ bank !! line cursor
  replace_slots slot = splice (line cursor) (line cursor + 1) [slot] bank
  join a b = fromJust $ Prefix.join a b
  split i chain = fromJust $ Prefix.split i chain

swingRight :: Workspace -> ([String], Workspace)
swingRight workspace@(Workspace { bac, cursor, bank })
  | line cursor /= lineFrom cursor || isLeft (bank !! line cursor)
  = (["should be a chain"], workspace)
  | column cursor == columnFrom cursor && column cursor == len
  = case chain |> Prefix.target |> Prefix.outgoing bac of
    edge : _ -> return workspace { bank = replace_slots (Right $ chain `join` edge) }
    _ -> (["no edge to extend"], workspace)
  | column cursor == columnFrom cursor && column cursor == len - 1
  = let
      (chain', edge) = split (len - 1) chain
      edges = chain' |> Prefix.target |> Prefix.outgoing bac
      edge' = edges |> findIndex (=== edge) |> fromJust |> (+ 1) |> (`mod` length edges) |> (edges !!)
    in
      return workspace { bank = replace_slots (Right $ chain' `join` edge') }
  | column cursor == columnFrom cursor
  = (["should at the end position or with selection"], workspace)
  | otherwise
  = let
      from = min (column cursor) (columnFrom cursor)
      to = max (column cursor) (columnFrom cursor)
      ((chain1, chain2), chain3) = first (split from) $ split to chain
      (prefix, suffix) = split (Prefix.length chain2 - 1) chain2
      suffixes = Prefix.suffixes chain2
      (prefix', suffix') =
        suffixes |> findIndex (\(pref, suff) -> pref ==~ prefix && suff === suffix) |> fromJust
        |> (+ 1) |> (`mod` length suffixes) |> (suffixes !!)
      chain' = chain1 `join` prefix' `join` suffix' `join` chain3
      to' = Prefix.length chain' - Prefix.length chain3
      (col, colFrom) = if column cursor < columnFrom cursor then (from, to') else (to', from)
    in
      return workspace {
        bank = replace_slots (Right chain'),
        cursor = Cursor (line cursor) col (line cursor) colFrom
      }
  where
  chain = fromRight $ bank !! line cursor
  len = Prefix.length chain
  replace_slots slot = splice (line cursor) (line cursor + 1) [slot] bank
  join a b = fromJust $ Prefix.join a b
  split i chain = fromJust $ Prefix.split i chain


updateBankBy :: (Chain -> [Chain]) -> Workspace -> Workspace
updateBankBy updater workspace@(Workspace { bac, bank, cursor }) =
  workspace { bank = concat bank', cursor = cursorAt line' 0 }
  where
  bank' = bank |> fmap \case
    Left str -> [Left str]
    Right chain -> do
      case updater chain of
        [] -> [Left $ concat $ Prefix.getStrings chain]
        chains -> chains |> fmap Right
  line' = take (line cursor) bank' |> concat |> length

insertResult :: [Slot] -> Workspace -> Workspace
insertResult slots workspace@(Workspace { cursor, bank }) =
  workspace { bank = bank', cursor = cursor' }
  where
  index = max (line cursor) (lineFrom cursor) + 1
  bank' = splice index index slots bank
  cursor' = if null slots then cursor else
    Cursor index 0 (index + length slots - 1) (slotLength (last slots))

isProperObject :: Chain -> Bool
isProperObject chain = Prefix.length chain == 0 && notNull (Prefix.getPreString chain)

isProperMorphism :: Chain -> Bool
isProperMorphism chain = Prefix.length chain > 0 && notNull (Prefix.getPreString chain)

inputToken :: InputControl m => PrefixBAC -> ExceptT [String] m String
inputToken bac = do
  str <- inputString "input a token:"
  str |> untilRightM \str -> do
    let tokens = split (== ' ') str |> filter notNull
    if length tokens /= 1 then
      Left $ inputString "input a token: (invalid token, try again)"
    else
      head tokens
      |> Prefix.searchString bac
      |> fmap (Prefix.recover (head tokens))
      |> listToMaybe
      |> maybe (return $ head tokens) \token ->
        Left $ inputString $
          "input a token: (conflict with " ++ token ++ ", try again)"

inputTokenExcept :: InputControl m => PrefixBAC -> String -> ExceptT [String] m String
inputTokenExcept bac str0 = do
  str <- inputString "input a token:"
  str |> untilRightM \strs -> do
    let tokens = split (== ' ') strs |> filter notNull
    if length tokens /= 1 then
      Left $ inputString "input a token: (invalid token, try again)"
    else
      head tokens
      |> Prefix.searchString bac
      |> fmap (Prefix.recover (head tokens))
      |> filter (/= str0)
      |> listToMaybe
      |> maybe (return $ head tokens) \token ->
        Left $ inputString $
          "input a token: (conflict with " ++ token ++ ", try again)"

inputTokens :: InputControl m => PrefixBAC -> Int -> ExceptT [String] m [String]
inputTokens bac n = do
  strs <- inputString $ "input " ++ show n ++ " tokens:"
  strs |> untilRightM \strs -> do
    let tokens = split (== ' ') strs |> filter notNull
    if length tokens /= n then
      Left $ inputString $ "input " ++ show n ++ " tokens: (invalid tokens, try again)"
    else
      tokens
      |> map (Prefix.searchString bac)
      |> zip tokens
      |> concatMap sequence
      |> fmap (uncurry Prefix.recover)
      |> listToMaybe
      |> maybe (return tokens) \token ->
        Left $ inputString $
          "input " ++ show n ++ " tokens: (conflict with " ++ token ++ ", try again)"


divideLeft :: Workspace -> ([String], Workspace)
divideLeft workspace =
  case getBankRange workspace of
    [Right chain1, Right chain2] ->
      case Prefix.dividel chain1 chain2 of
        Nothing -> (["they are not left-divisible"], workspace)
        Just [] -> (["no result"], workspace)
        Just results ->
          return $ insertResult (fmap Right results) workspace
    _ -> (["should be two chains"], workspace)

divideRight :: Workspace -> ([String], Workspace)
divideRight workspace =
  case getBankRange workspace of
    [Right chain1, Right chain2] ->
      case Prefix.divider chain1 chain2 of
        Nothing -> (["they are not right-divisible"], workspace)
        Just [] -> (["no result"], workspace)
        Just results ->
          return $ insertResult (fmap Right results) workspace
    _ -> (["should be two chains"], workspace)

search :: Workspace -> ([String], Workspace)
search workspace@(Workspace { bac }) =
  case getBankRange workspace of
    [Left str] | notNull str ->
      case Prefix.searchString bac str of
        [] -> (["nothing found"], workspace)
        results -> do
          let toString (GreaterBy suff) = take (length str - length suff) str
              toString (LessBy suff) = str ++ suff
              toString Equal = str
          return $ insertResult (results |> fmap (toString .> Left)) workspace
    _ -> (["should be a string"], workspace)

fallback :: Functor m => Workspace -> ExceptT [String] m Workspace -> m ([String], Workspace)
fallback workspace = runExceptT .> fmap \case
  Left messages -> (messages, workspace)
  Right res -> ([], res)

addEdge :: InputControl m => Workspace -> m ([String], Workspace)
addEdge workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.length chain > 0 -> return chain
    _ -> throwE ["should be a chain"]
  str <- inputToken bac
  (bac', updater) <- Prefix.addEdge chain str bac
    ?? ["fail to add an edge"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)
    |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]

removeEdge :: InputControl m => Workspace -> m ([String], Workspace)
removeEdge workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.length chain == 1 -> return chain
    _ -> throwE ["should be an edge"]
  (bac', updater) <- Prefix.removeEdge chain bac
    ?? ["fail to remove an edge"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> maybeToList)

alterEdge :: InputControl m => Workspace -> m ([String], Workspace)
alterEdge workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.length chain == 1 -> return chain
    _ -> throwE ["should be an edge"]
  str <- inputTokenExcept bac (head $ Prefix.getStrings chain)
  (bac', updater) <- Prefix.alterEdge chain str bac
    ?? ["fail to alter an edge"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)

data AlternativePathOptionSlot = AlternativePathOptionSlot Chain Chain Chain

instance Show AlternativePathOptionSlot where
  show (AlternativePathOptionSlot chain1 chain2 chain3) =
    concat (Prefix.getStrings chain1)
    ++ " * " ++ concat (Prefix.getStrings chain2)
    ++ " ~ " ++ concat (Prefix.getStrings chain3)

removeMorphism :: InputControl m => Workspace -> m ([String], Workspace)
removeMorphism workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.isNondecomposable chain -> return chain
    _ -> throwE ["should be a nondecomposable edge"]
  let (chains1, chains2) = Prefix.needAlternativePathsBeforeRemovingMorphism bac chain |> fromJust
  unless (null chains1 && null chains2) $
    throwE $ chains1 ++ chains2 |> fmap (Prefix.getStrings .> concat) |> ("need direct edges:" :)
  let str = head $ Prefix.getStrings chain
  let (altss1, altss2) = Prefix.getAlternativeRules bac chain |> fromJust
  let optionss1 = altss1 |> fmap \(chains, chain) -> chains |> fmap (, chain)
  let optionss2 = altss2 |> fmap \(chains, chain) -> chains |> fmap (, chain)
  alts1 <- optionss1 |> traverse (
    fmap (\(chain3, chain1) -> AlternativePathOptionSlot chain1 chain chain3)
    .> inputSelection "select an incoming alternative rule:"
    .> fmap \(AlternativePathOptionSlot chain1 _ chain3) -> (chain3, chain1))
  alts2 <- optionss2 |> traverse (
    fmap (\(chain3, chain2) -> AlternativePathOptionSlot chain chain2 chain3)
    .> inputSelection "select an outgoing alternative rule:"
    .> fmap \(AlternativePathOptionSlot _ chain2 chain3) -> (chain3, chain2))
  (bac', updater) <- Prefix.removeMorphism chain (alts1, alts2) bac
    ?? ["fail to remove a morphism"]
  return $
    workspace { bac = bac' }
    |> updateBankBy updater

removeObject :: InputControl m => Workspace -> m ([String], Workspace)
removeObject workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | isProperObject chain -> return chain
    _ -> throwE ["should be a node"]
  let node = Prefix.source chain
  let chains = Prefix.needAlternativePathsBeforeRemovingObject bac node
  unless (null chains) $
    throwE $ chains |> fmap (Prefix.getStrings .> concat) |> ("need to add direct edges:" :)
  let altss = Prefix.getObjectAlternativeRules bac node
  let optionss = altss |> fmap \(chains, chain2) -> chains |> fmap (, chain2)
  alts <- optionss |> traverse (
    fmap (\(chain3, (chain1, chain2)) -> AlternativePathOptionSlot chain1 chain2 chain3)
    .> inputSelection "select an alternative rule:"
    .> fmap \(AlternativePathOptionSlot chain1 chain2 chain3) -> (chain3, (chain1, chain2)))
  (bac', updater) <- Prefix.removeObject (Prefix.source chain) alts bac
    ?? ["fail to remove an object"]
  return $
    workspace { bac = bac' }
    |> updateBankBy updater

addObject :: InputControl m => Workspace -> m ([String], Workspace)
addObject workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.length chain == 0 -> return chain
    _ -> throwE ["should be a node"]
  str <- inputToken bac
  (bac', updater) <- Prefix.addObject (Prefix.source chain) str bac
    ?? ["fail to add an object"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)
    |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]

interpolateObject :: InputControl m => Workspace -> m ([String], Workspace)
interpolateObject workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | Prefix.length chain > 0 -> return chain
    _ -> throwE ["should be a chain"]
  strs <- inputTokens bac 2
  let [str1, str2] = strs
  (bac', updater) <- Prefix.interpolateObject chain (str1, str2) bac
    ?? ["fail to interpolate an object"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)
    |> insertResult [Right $ fromJust $ Prefix.fromString bac' (str1 ++ str2)]

newtype ChainOptionSlot = ChainOptionSlot Chain

instance Show ChainOptionSlot where
  show (ChainOptionSlot chain) =
    case Prefix.getStrings chain of
      [] -> "(" ++ Prefix.getPreString chain ++ ")"
      tokens -> concat tokens

splitMorphism :: InputControl m => Workspace -> m ([String], Workspace)
splitMorphism workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | isProperMorphism chain -> return chain
    _ -> throwE ["should be a non-initial chain"]
  let groups = Prefix.partitionPrefixesSuffixes chain
  let options = groups |> fmap (fst .> head .> uncurry Prefix.join .> fromJust)
  unless (length options > 1) $ throwE ["nothing can split"]
  partition <-
    options
    |> fmap ChainOptionSlot
    |> inputPartition "partition chains to split:"
    |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
  unless (length partition > 1) $ throwE ["nothing to split"]
  (bac', updater) <- Prefix.splitMorphism partition bac
    ?? ["fail to split the morphism"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)

splitObjectIncoming :: InputControl m => Workspace -> m ([String], Workspace)
splitObjectIncoming workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | isProperObject chain -> return chain
    _ -> throwE ["should be a node"]
  let groups = Prefix.partitionIncoming bac (Prefix.source chain)
  let options = fmap head groups
  unless (length options > 1) $ throwE ["nothing can split"]
  partition <-
    options
    |> fmap ChainOptionSlot
    |> inputPartition "partition chains to split:"
    |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
  unless (length partition > 1) $ throwE ["nothing to split"]
  strs <- inputTokens bac (length partition)
  (bac', updater) <- Prefix.splitObjectIncoming (Prefix.source chain) (strs `zip` partition) bac
    ?? ["fail to split the morphism"]
  return $
    workspace { bac = bac' }
    |> updateBankBy updater

splitObjectOutgoing :: InputControl m => Workspace -> m ([String], Workspace)
splitObjectOutgoing workspace@(Workspace { bac }) = fallback workspace do
  chain <- case getBankRange workspace of
    [Right chain] | isProperObject chain -> return chain
    _ -> throwE ["should be a node"]
  let groups = Prefix.partitionOutgoing (Prefix.source chain)
  let options = fmap head groups
  unless (length options > 1) $ throwE ["nothing can split"]
  partition <-
    options
    |> fmap ChainOptionSlot
    |> inputPartition "partition chains to split:"
    |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
  unless (length partition > 1) $ throwE ["nothing to split"]
  strs <- inputTokens bac (length partition)
  (bac', updater) <- Prefix.splitObjectOutgoing (Prefix.source chain) (strs `zip` partition) bac
    ?? ["fail to split the morphism"]
  return $
    workspace { bac = bac' }
    |> updateBankBy updater

mergeMorphisms :: InputControl m => Workspace -> m ([String], Workspace)
mergeMorphisms workspace@(Workspace { bac }) = fallback workspace do
  slots <- case getBankRange workspace of
    slots | notNull slots && all (either (const False) isProperMorphism) slots -> return slots
    _ -> throwE ["should be non-initial chains"]
  let chains = slots |> fmap fromRight
  let groups = Prefix.findMergableChains bac (head chains)

  (chain1, chain2) <- case chains of
    [chain] -> do
      let options = groups |> filter ((==~ chain) .> not)
      unless (notNull options) $ throwE ["nothing can merge"]
      chain' <-
        options
        |> fmap ChainOptionSlot
        |> inputSelection "select a chain to merge:"
        |> fmap \(ChainOptionSlot c) -> c
      return (chain, chain')
    [chain1, chain2] -> do
      when (chain1 ==~ chain2) $
        throwE ["two chains are the same morphism"]
      unless (groups |> any (==~ chain2)) $
        throwE ["cannot merge those morphisms"]
      return (chain1, chain2)
    _ -> throwE ["too many morphisms to merge"]

  (bac', updater) <- Prefix.mergeMorphsisms [chain1, chain2] bac
    ?? ["fail to merge morphisms"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)

newtype ZipOptionSlot = ZipOptionSlot [(Chain, Chain)]

instance Show ZipOptionSlot where
  show (ZipOptionSlot []) = "(no rule is needed)"
  show (ZipOptionSlot eq) =
    eq
    |> fmap (both (Prefix.getStrings .> concat))
    |> concatMap \(s1, s2) -> s1 ++ " ~ " ++ s2 ++ "; "

mergeObjectsOutgoing :: InputControl m => Workspace -> m ([String], Workspace)
mergeObjectsOutgoing workspace@(Workspace { bac }) = fallback workspace do
  slots <- case getBankRange workspace of
    slots | notNull slots && all (either (const False) isProperObject) slots -> return slots
    _ -> throwE ["should be nodes"]
  let nodes = slots |> fmap (fromRight .> Prefix.source)
  let groups = Prefix.findIncomingZippableObjects bac (head nodes)

  (node1, node2) <- case nodes of
    [node] -> do
      let options = groups |> fmap fst |> filter ((==- node) .> not)
      unless (notNull options) $ throwE ["nothing can merge"]
      node' <-
        options
        |> fmap (Prefix.id .> ChainOptionSlot)
        |> inputSelection "select a node to merge:"
        |> fmap \(ChainOptionSlot c) -> Prefix.source c
      return (node, node')
    [node1, node2] -> do
      when (node1 ==- node2) $
        throwE ["two nodes are the same object"]
      unless (groups |> fmap fst |> any (==- node2)) $
        throwE ["cannot merge those objects"]
      return (node1, node2)
    _ -> throwE ["too many nodes to merge"]

  let incomings1 = groups |> find (fst .> (==- node1)) |> fromJust |> snd |> head
  let options = groups |> find (fst .> (==- node2)) |> fromJust |> snd
  incomings2 <-
    options
    |> fmap (zip incomings1 .> ZipOptionSlot)
    |> inputSelection "select a zip strategy:"
    |> fmap \(ZipOptionSlot opt) -> fmap snd opt

  (bac', updater) <- Prefix.mergeObjectsOutgoing [(node1, incomings1), (node2, incomings2)] bac
    ?? ["fail to merge objects"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)

mergeObjectsIncoming :: InputControl m => Workspace -> m ([String], Workspace)
mergeObjectsIncoming workspace@(Workspace { bac }) = fallback workspace do
  slots <- case getBankRange workspace of
    slots | notNull slots && all (either (const False) isProperObject) slots -> return slots
    _ -> throwE ["should be nodes"]
  let nodes = slots |> fmap (fromRight .> Prefix.source)
  let groups = Prefix.findOutgoingZippableObjects bac (head nodes)

  (node1, node2) <- case nodes of
    [node] -> do
      let options = groups |> fmap fst |> filter ((==- node) .> not)
      unless (notNull options) $ throwE ["nothing can merge"]
      node' <-
        options
        |> fmap (Prefix.id .> ChainOptionSlot)
        |> inputSelection "select a node to merge:"
        |> fmap \(ChainOptionSlot c) -> Prefix.source c
      return (node, node')
    [node1, node2] -> do
      when (node1 ==- node2) $
        throwE ["two nodes are the same object"]
      unless (groups |> fmap fst |> any (==- node2)) $
        throwE ["cannot merge those objects"]
      return (node1, node2)
    _ -> throwE ["too many nodes to merge"]

  let outgoings1 = groups |> find (fst .> (==- node1)) |> fromJust |> snd |> head
  let options = groups |> find (fst .> (==- node2)) |> fromJust |> snd
  outgoings2 <-
    options
    |> fmap (zip outgoings1 .> ZipOptionSlot)
    |> inputSelection "select a zip strategy:"
    |> fmap \(ZipOptionSlot opt) -> fmap snd opt

  (bac', updater) <- Prefix.mergeObjectsIncoming [(node1, outgoings1), (node2, outgoings2)] bac
    ?? ["fail to merge objects"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)

data CofractionOptionSlot = CofractionOptionSlot String Prefix.Cofraction

instance Show CofractionOptionSlot where
  show (CofractionOptionSlot str (chain1, chain2)) =
    concat (Prefix.getStrings chain2) ++ " * " ++ str ++ " ~ " ++ concat (Prefix.getStrings chain1)

data FractionOptionSlot = FractionOptionSlot String Prefix.Fraction

instance Show FractionOptionSlot where
  show (FractionOptionSlot str (chain1, chain2)) =
    str ++ " * " ++ concat (Prefix.getStrings chain2) ++ " ~ " ++ concat (Prefix.getStrings chain1)

addMorphism :: InputControl m => Workspace -> m ([String], Workspace)
addMorphism workspace@(Workspace { bac }) = fallback workspace do
  (node1, node2) <- case getBankRange workspace of
    [Right chain] | isProperMorphism chain ->
      return (Prefix.source chain, Prefix.target chain)
    [Right chain1, Right chain2] | isProperObject chain1 && isProperObject chain2 -> do
      let node1 = Prefix.source chain1
      let node2 = Prefix.source chain2
      unless (null $ fromJust $ Prefix.init bac node2 `Prefix.dividel` Prefix.init bac node1) $
        throwE ["invalid node order to add morphism"]
      return (node1, node2)
    _ -> throwE ["should be two nodes or a chain"]

  (optionss1, optionss2) <- Prefix.getPossibleDivisionRules bac node1 node2
    ?? ["cannot add a morphism"]

  str <- inputToken bac

  -- TODO: shrink options by compatibleDivisionRule
  cofractions <- optionss1 |> traverse \options1 ->
    options1
    |> fmap (CofractionOptionSlot str)
    |> inputSelection "select a cofraction rule:"
    |> fmap \(CofractionOptionSlot _ opt) -> opt
  fractions <- optionss2 |> traverse \options2 ->
    options2
    |> fmap (FractionOptionSlot str)
    |> inputSelection "select a fraction rule:"
    |> fmap \(FractionOptionSlot _ opt) -> opt
  unless (Prefix.compatibleDivisionRule bac (cofractions, fractions)) $
    throwE ["invalid rules"]
  (bac', updater) <- Prefix.addMorphism node1 node2 (cofractions, fractions) str bac
    ?? ["fail to add a morphism"]
  return $
    workspace { bac = bac' }
    |> updateBankBy (updater .> return)
    |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]


writeBAC :: FileAccessControl m => FilePath -> Workspace -> ExceptT [String] m Workspace
writeBAC filepath workspace@(Workspace { bac }) = do
  let contents = BAC.serializeWithValue id (Prefix.getBAC bac)
  _ <- writeString filepath contents
  return workspace { bac_filepath = Just filepath }

writeBank :: FileAccessControl m => FilePath -> Workspace -> ExceptT [String] m Workspace
writeBank filepath workspace@(Workspace { bank }) = do
  let contents = bank |> fmap slotToString |> intercalate "\n"
  _ <- writeString filepath contents
  return workspace { bank_filepath = Just filepath }

readBAC :: FileAccessControl m => FilePath -> Workspace -> ExceptT [String] m Workspace
readBAC filepath workspace = do
  contents <- readString filepath
  case BAC.deserializeWithValue Just contents of
    Left err -> throwE ["fail to parse bac: " ++ show err]
    Right bac -> case Prefix.fromBAC bac of
      Nothing -> throwE ["not a prefix bac"]
      Just pbac -> return workspace { bac = pbac, bac_filepath = Just filepath }

readBank :: FileAccessControl m => FilePath -> Workspace -> ExceptT [String] m Workspace
readBank filepath workspace@(Workspace { bac }) = do
  contents <- readString filepath
  let bank = contents |> split (== '\n') |> fmap (slotFromString bac)
  return workspace { bank = bank, bank_filepath = Just filepath }

readBankAppend :: FileAccessControl m => FilePath -> Workspace -> ExceptT [String] m Workspace
readBankAppend filepath workspace@(Workspace { bac, bank }) = do
  contents <- readString filepath
  let bank' = contents |> split (== '\n') |> fmap (slotFromString bac)
  return workspace { bank = bank ++ bank' }

saveBAC :: (FileAccessControl m, InputControl m) => FilePath -> Workspace -> m ([String], Workspace)
saveBAC filepath workspace = writeBAC filepath workspace |> runExceptT >>= \case
  Left messages -> return ("fail to save BAC" : messages, workspace)
  Right workspace' -> return (["BAC is saved to " ++ filepath], workspace')

saveBank :: (FileAccessControl m, InputControl m) => FilePath -> Workspace -> m ([String], Workspace)
saveBank filepath workspace = writeBank filepath workspace |> runExceptT >>= \case
  Left messages -> return ("fail to save Bank" : messages, workspace)
  Right workspace' -> return (["bank is saved to " ++ filepath], workspace')

openBAC :: (FileAccessControl m, InputControl m) => FilePath -> Workspace -> m ([String], Workspace)
openBAC filepath workspace = readBAC filepath workspace |> runExceptT >>= \case
  Left messages -> return ("fail to open BAC" : messages, workspace)
  Right workspace' -> return (["BAC is open from " ++ filepath], workspace')

openBank :: (FileAccessControl m, InputControl m) => FilePath -> Workspace -> m ([String], Workspace)
openBank filepath workspace = readBank filepath workspace |> runExceptT >>= \case
  Left messages -> return ("fail to open Bank" : messages, workspace)
  Right workspace' -> return (["bank is open from " ++ filepath], workspace')

appendBank :: (FileAccessControl m, InputControl m) => FilePath -> Workspace -> m ([String], Workspace)
appendBank filepath workspace = readBankAppend filepath workspace |> runExceptT >>= \case
  Left messages -> return ("fail to open Bank" : messages, workspace)
  Right workspace' -> return (["bank is appended from " ++ filepath], workspace')


getFilePath :: Workspace -> ([String], Workspace)
getFilePath workspace@(Workspace { bac_filepath, bank_filepath }) =
  ([
    maybe "no BAC filepath" ("BAC filepath is " ++) bac_filepath,
    maybe "no bank filepath" ("bank filepath is " ++) bank_filepath
  ], workspace)

saveAll :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
saveAll workspace@(Workspace { bac_filepath, bank_filepath }) = do
  (messages1, workspace') <- case bac_filepath of
    Nothing -> saveBACAs workspace
    Just filepath -> saveBAC filepath workspace
  (messages2, workspace'') <- case bank_filepath of
    Nothing -> saveBankAs workspace'
    Just filepath -> saveBank filepath workspace'
  return (messages1 ++ messages2, workspace'')

askSaveAll :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
askSaveAll workspace@(Workspace { bac_filepath, bank_filepath }) = do
  res <- runExceptT $ inputString "save BAC and bank?"
  case res of
    Left messages -> return (messages, workspace)
    Right _ -> saveAll workspace

saveBACAs :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
saveBACAs workspace = do
  res <- runExceptT $ inputString "save BAC as:"
  case res of
    Left messages -> return (messages, workspace)
    Right filepath -> saveBAC filepath workspace

saveBankAs :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
saveBankAs workspace = do
  res <- runExceptT $ inputString "save bank as:"
  case res of
    Left messages -> return (messages, workspace)
    Right filepath -> saveBank filepath workspace

openBACFrom :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
openBACFrom workspace = do
  res <- runExceptT $ inputString "open BAC from:"
  case res of
    Left messages -> return (messages, workspace)
    Right filepath -> openBAC filepath workspace

openBankFrom :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
openBankFrom workspace = do
  res <- runExceptT $ inputString "open bank from:"
  case res of
    Left messages -> return (messages, workspace)
    Right filepath -> openBank filepath workspace

appendBankFrom :: (FileAccessControl m, InputControl m) => Workspace -> m ([String], Workspace)
appendBankFrom workspace = do
  res <- runExceptT $ inputString "append bank from:"
  case res of
    Left messages -> return (messages, workspace)
    Right filepath -> appendBank filepath workspace


showContents :: Workspace -> ([String], Workspace)
showContents workspace@(Workspace { bac }) = (contents, workspace)
  where
  contents = BAC.serializeWithValue id (Prefix.getBAC bac) |> split (== '\n')

refineContents :: Workspace -> ([String], Workspace)
refineContents workspace@(Workspace { bac }) =
  return $ workspace { bac = bac' } |> updateBankBy (updater .> return)
  where
  (bac', updater) = Prefix.refine bac
