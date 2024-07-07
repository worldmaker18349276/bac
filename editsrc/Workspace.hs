{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Workspace where

import Control.Monad (guard, when)
import Data.Bifunctor (first)
import Data.Char (isPrint)
import Data.Either (isLeft, isRight)
import Data.Either.Extra (maybeToEither)
import Data.List (find, findIndex)
import Data.List.Extra (notNull, split)
import Data.Maybe (fromJust, fromMaybe, isJust, listToMaybe, maybeToList)
import Data.Tuple.Extra (both)

import BAC.Prefix (Chain, Node, PrefixBAC, PrefixOrdering (..), (==-), (===), (==~))
import qualified BAC.Prefix as Prefix
import Utils


showChain :: Chain -> String
showChain chain = "(" ++ Prefix.getPreString chain ++ ")" ++ concat (Prefix.getStrings chain)

data Cursor = Cursor { line :: Int, column :: Int, lineFrom :: Int, columnFrom :: Int }

type Slot = Either String Chain

data Workspace = Workspace {
  bac :: PrefixBAC,
  buffer :: [Slot],
  cursor :: Cursor
}

class Monad m => Control m where
  inputString :: String -> m String
  inputSelection :: Show a => String -> [a] -> m a
  inputPartition :: Show a => String -> [a] -> m [[a]]

data Action =
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
  deriving (Show, Enum, Bounded)


runAction :: Control m => Action -> Workspace -> m (Either [String] Workspace)
runAction MoveUp = moveUp .> return .> return
runAction MoveDown = moveDown .> return .> return
runAction MoveLeft = moveLeft .> return .> return
runAction MoveRight = moveRight .> return .> return
runAction MoveHome = moveHome .> return .> return
runAction MoveEnd = moveEnd .> return .> return
runAction DragUp = dragUp .> return .> return
runAction DragDown = dragDown .> return .> return
runAction SelectUp = selectUp .> return .> return
runAction SelectDown = selectDown .> return .> return
runAction SelectLeft = selectLeft .> return .> return
runAction SelectRight = selectRight .> return .> return
runAction SelectHome = selectHome .> return .> return
runAction SelectEnd = selectEnd .> return .> return
runAction Dup = dup .> return .> return
runAction NewSlot = newSlot .> return .> return
runAction Join = join .> return
runAction DeleteBackward = deleteBackward .> return
runAction DeleteSlot = deleteSlot .> return
runAction ChangeType = changeType .> return
runAction InitialChain = initialChain .> return
runAction IsNondecomposable = isNondecomposable .> return
runAction AreSameMorphism = areSameMorphism .> return
runAction AreUnsplittable = areUnsplittable .> return
runAction IsValidBAC = isValidBAC .> return
runAction SwingLeft = swingLeft .> return
runAction SwingRight = swingRight .> return
runAction DivideLeft = divideLeft
runAction DivideRight = divideRight
runAction Search = search
runAction AddEdge = addEdge
runAction RemoveEdge = removeEdge
runAction AlterEdge = alterEdge
runAction RemoveMorphism = removeMorphism
runAction RemoveObject = removeObject
runAction AddMorphism = addMorphism
runAction AddObject = addObject
runAction InterpolateObject = interpolateObject
runAction SplitMorphism = splitMorphism
runAction SplitObjectOutgoing = splitObjectOutgoing
runAction SplitObjectIncoming = splitObjectIncoming
runAction MergeMorphisms = mergeMorphisms
runAction MergeObjectsOutgoing = mergeObjectsOutgoing
runAction MergeObjectsIncoming = mergeObjectsIncoming


cursorAt :: Int -> Int -> Cursor
cursorAt line column = Cursor line column line column

selectLines :: Workspace -> Int -> Int -> Cursor
selectLines workspace line_from line_to =
  if line_from <= line_to then
    Cursor line_to (slotLength (buffer workspace !! line_to)) line_from 0
  else
    Cursor line_to 0 line_from (slotLength (buffer workspace !! line_from))

slotLength :: Slot -> Int
slotLength (Left str) = length str
slotLength (Right chain) = Prefix.length chain

getBuffers :: Workspace -> [Slot]
getBuffers (Workspace { cursor, buffer }) =
  buffer
  |> range
    (min (line cursor) (lineFrom cursor))
    (max (line cursor) (lineFrom cursor) + 1)

getBuffer :: Workspace -> Slot
getBuffer (Workspace { cursor, buffer }) = buffer !! line cursor

getPart :: Workspace -> Maybe Slot
getPart workspace@(Workspace { cursor })
  | line cursor /= lineFrom cursor = Nothing
  | otherwise = case getBuffer workspace of
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
moveDown workspace@(Workspace { cursor, buffer })
  | line cursor < length buffer - 1
  = workspace { cursor = cursorAt (line cursor + 1) 0 }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) 0 }

moveUp :: Workspace -> Workspace
moveUp workspace@(Workspace { cursor, buffer })
  | line cursor > 0
  = workspace { cursor = cursorAt (line cursor - 1) 0 }
  | otherwise
  = workspace { cursor = cursorAt (line cursor) 0 }

moveRight :: Workspace -> Workspace
moveRight workspace@(Workspace { cursor, buffer })
  | column cursor < slotLength (buffer !! line cursor)
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
moveEnd workspace@(Workspace { cursor, buffer }) =
  workspace { cursor = cursorAt (line cursor) (slotLength (buffer !! line cursor)) }

moveHome :: Workspace -> Workspace
moveHome workspace@(Workspace { cursor }) =
  workspace { cursor = cursorAt (line cursor) 0 }

dragDown :: Workspace -> Workspace
dragDown workspace@(Workspace { cursor, buffer })
  | to < length buffer
  = workspace {
      cursor = cursor { line = line cursor + 1, lineFrom = lineFrom cursor + 1 },
      buffer = buffer |> rangeTo from <> range to (to + 1) <> range from to <> rangeFrom (to + 1)
    }
  | otherwise
  = workspace
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1

dragUp :: Workspace -> Workspace
dragUp workspace@(Workspace { cursor, buffer })
  | from > 0
  = workspace {
      cursor = cursor { line = line cursor - 1, lineFrom = lineFrom cursor - 1 },
      buffer = buffer |> rangeTo (from - 1) <> range from to <> range (from - 1) from <> rangeFrom to
    }
  | otherwise
  = workspace
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1

selectDown :: Workspace -> Workspace
selectDown workspace@(Workspace { cursor, buffer })
  | line cursor < length buffer - 1
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor + 1) }
  | otherwise
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor) }

selectUp :: Workspace -> Workspace
selectUp workspace@(Workspace { cursor, buffer })
  | line cursor > 0
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor - 1) }
  | otherwise
  = workspace { cursor = selectLines workspace (lineFrom cursor) (line cursor) }

selectRight :: Workspace -> Workspace
selectRight workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor
  = workspace
  | column cursor < slotLength (buffer !! line cursor)
  = workspace { cursor = cursor { column = column cursor + 1 } }
  | otherwise
  = workspace

selectLeft :: Workspace -> Workspace
selectLeft workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor
  = workspace
  | column cursor > 0
  = workspace { cursor = cursor { column = column cursor - 1 } }
  | otherwise
  = workspace

selectEnd :: Workspace -> Workspace
selectEnd workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor
  = workspace
  | otherwise
  = workspace { cursor = cursor { column = slotLength (buffer !! line cursor) } }

selectHome :: Workspace -> Workspace
selectHome workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor
  = workspace
  | otherwise
  = workspace { cursor = cursor { column = 0 } }

dup :: Workspace -> Workspace
dup workspace@(Workspace { cursor, buffer }) =
  workspace {
    buffer = splice dup_line dup_line dup_slots buffer,
    cursor = dup_cursor
  }
  where
  dup_slots =
    if line cursor == lineFrom cursor && column cursor == columnFrom cursor then
      [buffer !! line cursor]
    else
      getPart workspace |> maybe (getBuffers workspace) (: [])
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
newSlot workspace@(Workspace { cursor, buffer }) =
  workspace {
    buffer = splice line' line' [Left ""] buffer,
    cursor = cursorAt line' 0
  }
  where
  line' = max (line cursor) (lineFrom cursor) + 1

join :: Workspace -> Either [String] Workspace
join workspace@(Workspace { cursor, buffer })
  | all isLeft buffer'
  = return workspace {
      buffer = splice from to [Left $ concatMap fromLeft buffer'] buffer,
      cursor = cursorAt from 0
    }
  | all isRight buffer'
  = case foldl1M Prefix.join $ fmap fromRight buffer' of
    Just join_chain ->
      return workspace {
        buffer = splice from to [Right join_chain] buffer,
        cursor = cursorAt from 0
      }
    Nothing -> Left ["cannot join those chains"]
  | otherwise
  = Left ["cannot join strings and chains"]
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  buffer' = range from to buffer

input :: String -> Workspace -> Either [String] Workspace
input str workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor || isRight (buffer !! line cursor)
  = Left ["should on a string slot"]
  | not (all isPrint str)
  = Left ["cannot input non-printable character"]
  | otherwise
  = return workspace {
      buffer =
        buffer
        |> rangeTo (line cursor)
          <> const [Left $ splice from to str $ fromLeft (buffer !! line cursor)]
          <> rangeFrom (line cursor + 1),
      cursor = cursorAt (line cursor) col
    }
  where
  from = min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
  col = from + length str

deleteBackward :: Workspace -> Either [String] Workspace
deleteBackward workspace@(Workspace { cursor, buffer })
  | line cursor /= lineFrom cursor || slotLength (buffer !! line cursor) == 0
  = let
      line' = min (line cursor) (lineFrom cursor) - 1
      cursor' = if line' < 0 then cursorAt 0 0 else cursorAt line' (slotLength (buffer !! line'))
    in
      return workspace { buffer = replace_buffer [], cursor = cursor' }
  | otherwise
  = case buffer !! line cursor of
    Left str ->
      return workspace {
        buffer = replace_buffer [Left $ splice from to "" str],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 && to == Prefix.length chain && column cursor < columnFrom cursor ->
      return workspace {
        buffer = replace_buffer [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 && to == Prefix.length chain && column cursor > columnFrom cursor ->
      return workspace {
        buffer = replace_buffer [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | to == Prefix.length chain ->
      return workspace {
        buffer = replace_buffer [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain | from == 0 ->
      return workspace {
        buffer = replace_buffer [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
      }
    Right chain ->
      Left ["can only delete end of chains"]
  where
  from =
    if column cursor == columnFrom cursor && column cursor /= 0 then
      column cursor - 1
    else
      min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
  replace_buffer slots = if null buffer' then [Left ""] else buffer'
    where
    from = min (line cursor) (lineFrom cursor)
    to = max (line cursor) (lineFrom cursor) + 1
    buffer' = splice from to slots buffer

deleteSlot :: Workspace -> Either [String] Workspace
deleteSlot workspace@(Workspace { cursor, buffer }) =
  return workspace { buffer = replace_buffer [], cursor = cursorAt line' 0 }
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  line' = max (from - 1) 0
  replace_buffer slots = if null buffer' then [Left ""] else buffer'
    where
    from = min (line cursor) (lineFrom cursor)
    to = max (line cursor) (lineFrom cursor) + 1
    buffer' = splice from to slots buffer

changeType :: Workspace -> Either [String] Workspace
changeType workspace@(Workspace { bac, cursor, buffer })
  | line cursor /= lineFrom cursor
  = Left ["should on a single slot"]
  | otherwise
  = case buffer !! line cursor of
    Right chain ->
      return workspace {
        buffer = replace_buffer (Left $ concat $ Prefix.getStrings chain),
        cursor = cursorAt (line cursor) 0
      }
    Left str | null str ->
        return workspace {
          buffer = replace_buffer (Right $ Prefix.id $ Prefix.root bac),
          cursor = cursorAt (line cursor) 0
        }
    Left str -> case Prefix.fromString bac str of
      Nothing -> Left ["not a valid chain"]
      Just chain ->
        return workspace {
          buffer = replace_buffer (Right chain),
          cursor = cursorAt (line cursor) 0
        }
  where
  replace_buffer slot = splice (line cursor) (line cursor + 1) [slot] buffer

initialChain :: Workspace -> Either [String] Workspace
initialChain workspace@(Workspace { bac, cursor, buffer })
  | line cursor /= lineFrom cursor || isLeft (buffer !! line cursor) || slotLength (buffer !! line cursor) /= 0
  = Left ["should be a node"]
  | otherwise
  = let
      pretoken = Prefix.getPreString $ fromRight $ buffer !! line cursor
      init_chain =
        if null pretoken then
          Prefix.id (Prefix.root bac)
        else
          fromJust (Prefix.fromString bac pretoken)
    in return workspace {
        buffer = splice (line cursor) (line cursor + 1) [Right init_chain] buffer,
        cursor = cursorAt (line cursor) (Prefix.length init_chain)
      }

isNondecomposable :: Workspace -> Either [String] Workspace
isNondecomposable workspace@(Workspace { bac, cursor, buffer })
  | line cursor /= lineFrom cursor || isLeft (buffer !! line cursor)
  = Left ["should be a chain"]
  | otherwise
  = Left [show $ Prefix.isNondecomposable $ fromRight $ buffer !! line cursor]

areSameMorphism :: Workspace -> Either [String] Workspace
areSameMorphism workspace
  | not (all isRight $ getBuffers workspace)
  = Left ["should be chains"]
  | otherwise
  = Left [getBuffers workspace |> fmap fromRight |> allSameBy (==~) |> show]

areUnsplittable :: Workspace -> Either [String] Workspace
areUnsplittable workspace
  | not (all isRight $ getBuffers workspace)
  = Left ["should be chains"]
  | otherwise
  = Left [getBuffers workspace |> fmap fromRight |> allSameBy Prefix.isUnsplittable |> show]

isValidBAC :: Workspace -> Either [String] Workspace
isValidBAC workspace@(Workspace { bac }) = Left [show (Prefix.validate bac)]

swingLeft :: Workspace -> Either [String] Workspace
swingLeft workspace@(Workspace { bac, cursor, buffer })
  | line cursor /= lineFrom cursor || isLeft (buffer !! line cursor)
  = Left ["should be a chain"]
  | column cursor == columnFrom cursor && column cursor == 0
  = case chain |> Prefix.source |> Prefix.incoming bac of
    edge : _ -> return workspace {
      buffer = replace_buffer (Right $ edge `join` chain),
      cursor = cursorAt (line cursor) 1
    }
    _ -> Left ["no edge to extend"]
  | column cursor == columnFrom cursor && column cursor == 1
  = let
      (edge, chain') = split 1 chain
      edges = chain' |> Prefix.source |> Prefix.incoming bac
      edge' = edges |> findIndex (=== edge) |> fromJust |> (+ 1) |> (`mod` length edges) |> (edges !!)
    in
      return workspace { buffer = replace_buffer (Right $ edge' `join` chain') }
  | column cursor == columnFrom cursor
  = Left ["should at the start position or with selection"]
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
        buffer = replace_buffer (Right chain'),
        cursor = Cursor (line cursor) col (line cursor) colFrom
      }
  where
  chain = fromRight $ buffer !! line cursor
  replace_buffer slot = splice (line cursor) (line cursor + 1) [slot] buffer
  join a b = fromJust $ Prefix.join a b
  split i chain = fromJust $ Prefix.split i chain

swingRight :: Workspace -> Either [String] Workspace
swingRight workspace@(Workspace { bac, cursor, buffer })
  | line cursor /= lineFrom cursor || isLeft (buffer !! line cursor)
  = Left ["should be a chain"]
  | column cursor == columnFrom cursor && column cursor == len
  = case chain |> Prefix.target |> Prefix.outgoing bac of
    edge : _ -> return workspace { buffer = replace_buffer (Right $ chain `join` edge) }
    _ -> Left ["no edge to extend"]
  | column cursor == columnFrom cursor && column cursor == len - 1
  = let
      (chain', edge) = split (len - 1) chain
      edges = chain' |> Prefix.target |> Prefix.outgoing bac
      edge' = edges |> findIndex (=== edge) |> fromJust |> (+ 1) |> (`mod` length edges) |> (edges !!)
    in
      return workspace { buffer = replace_buffer (Right $ chain' `join` edge') }
  | column cursor == columnFrom cursor
  = Left ["should at the end position or with selection"]
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
        buffer = replace_buffer (Right chain'),
        cursor = Cursor (line cursor) col (line cursor) colFrom
      }
  where
  chain = fromRight $ buffer !! line cursor
  len = Prefix.length chain
  replace_buffer slot = splice (line cursor) (line cursor + 1) [slot] buffer
  join a b = fromJust $ Prefix.join a b
  split i chain = fromJust $ Prefix.split i chain


updateBufferBy :: (Chain -> [Chain]) -> Workspace -> Workspace
updateBufferBy updater workspace@(Workspace { bac, buffer, cursor }) =
  workspace { buffer = concat buffer', cursor = cursorAt line' 0 }
  where
  buffer' = buffer |> fmap \case
    Left str -> [Left str]
    Right chain -> do
      case updater chain of
        [] -> [Left $ concat $ Prefix.getStrings chain]
        chains -> chains |> fmap Right
  line' = take (line cursor) buffer' |> concat |> length

insertResult :: [Slot] -> Workspace -> Workspace
insertResult slots workspace@(Workspace { cursor, buffer }) =
  workspace { buffer = buffer', cursor = cursor' }
  where
  index = max (line cursor) (lineFrom cursor) + 1
  buffer' = splice index index slots buffer
  cursor' = if null slots then cursor else
    Cursor index 0 (index + length slots - 1) (slotLength (last slots))

isProperObject :: Chain -> Bool
isProperObject chain = Prefix.length chain == 0 && notNull (Prefix.getPreString chain)

isProperMorphism :: Chain -> Bool
isProperMorphism chain = Prefix.length chain > 0 && notNull (Prefix.getPreString chain)

inputToken :: Control m => PrefixBAC -> m String
inputToken bac = do
  str <- inputString "input a token:"
  str |> untilRightM \strs -> do
    let tokens = split (== ' ') strs |> filter notNull
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

inputTokenExcept :: Control m => PrefixBAC -> String -> m String
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

inputTokens :: Control m => PrefixBAC -> Int -> m [String]
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
          "input " ++ show n ++ " tokens: (conflict with" ++ token ++ ", try again)"


divideLeft :: Control m => Workspace -> m (Either [String] Workspace)
divideLeft workspace =
  case getBuffers workspace of
    [Right chain1, Right chain2] ->
      case Prefix.dividel chain1 chain2 of
        Nothing -> return $ Left ["they are not left-divisible"]
        Just [] -> return $ Left ["no result"]
        Just results ->
          return $ Right $ insertResult (fmap Right results) workspace
    _ -> return $ Left ["should be two chains"]

divideRight :: Control m => Workspace -> m (Either [String] Workspace)
divideRight workspace =
  case getBuffers workspace of
    [Right chain1, Right chain2] ->
      case Prefix.divider chain1 chain2 of
        Nothing -> return $ Left ["they are not right-divisible"]
        Just [] -> return $ Left ["no result"]
        Just results ->
          return $ Right $ insertResult (fmap Right results) workspace
    _ -> return $ Left ["should be two chains"]

search :: Control m => Workspace -> m (Either [String] Workspace)
search workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Left str] | notNull str ->
      case Prefix.searchString bac str of
        [] -> return $ Left ["nothing found"]
        results -> do
          let toString (GreaterBy suff) = take (length str - length suff) str
              toString (LessBy suff) = str ++ suff
              toString Equal = str
          return $ Right $ insertResult (results |> fmap (toString .> Left)) workspace
    _ -> return $ Left ["should be a string"]

addEdge :: Control m => Workspace -> m (Either [String] Workspace)
addEdge workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.length chain > 0 -> do
      str <- inputToken bac
      case Prefix.addEdge chain str bac of
        Nothing -> return $ Left ["fail to add an edge"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy (updater .> return)
            |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]
    _ -> return $ Left ["should be a chain"]

removeEdge :: Control m => Workspace -> m (Either [String] Workspace)
removeEdge workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.length chain == 1 ->
      case Prefix.removeEdge chain bac of
        Nothing -> return $ Left ["fail to remove an edge"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy (updater .> maybeToList)
    _ -> return $ Left ["should be an edge"]

alterEdge :: Control m => Workspace -> m (Either [String] Workspace)
alterEdge workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.length chain == 1 -> do
      str <- inputTokenExcept bac (head $ Prefix.getStrings chain)
      case Prefix.alterEdge chain str bac of
        Nothing -> return $ Left ["fail to alter an edge"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy (updater .> return)
    _ -> return $ Left ["should be an edge"]

removeMorphism :: Control m => Workspace -> m (Either [String] Workspace)
removeMorphism workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.isNondecomposable chain -> do
      strs <- inputTokens bac 2
      let [str1, str2] = strs
      case Prefix.removeMorphism chain (str1, str2) bac of
        Nothing -> return $ Left ["fail to remove a morphism"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy updater
    _ -> return $ Left ["should be a nondecomposable edge"]

removeObject :: Control m => Workspace -> m (Either [String] Workspace)
removeObject workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperObject chain ->
      case Prefix.removeObject (Prefix.source chain) bac of
        Nothing -> return $ Left ["fail to remove an object"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy updater
    _ -> return $ Left ["should be a node"]

addObject :: Control m => Workspace -> m (Either [String] Workspace)
addObject workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.length chain == 0 -> do
      str <- inputToken bac
      case Prefix.addObject (Prefix.source chain) str bac of
        Nothing -> return $ Left ["fail to add an object"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy (updater .> return)
            |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]
    _ -> return $ Left ["should be a node"]

interpolateObject :: Control m => Workspace -> m (Either [String] Workspace)
interpolateObject workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | Prefix.length chain > 0 -> do
      strs <- inputTokens bac 2
      let [str1, str2] = strs
      case Prefix.interpolateObject chain (str1, str2) bac of
        Nothing -> return $ Left ["fail to interpolate an object"]
        Just (bac', updater) ->
          return $ Right $
            workspace { bac = bac' }
            |> updateBufferBy (updater .> return)
            |> insertResult [Right $ fromJust $ Prefix.fromString bac' (str1 ++ str2)]
    _ -> return $ Left ["should be a chain"]

newtype ChainOptionSlot = ChainOptionSlot Chain

instance Show ChainOptionSlot where
  show (ChainOptionSlot chain) =
    case Prefix.getStrings chain of
      [] -> "(" ++ Prefix.getPreString chain ++ ")"
      tokens -> concat tokens

splitMorphism :: Control m => Workspace -> m (Either [String] Workspace)
splitMorphism workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperMorphism chain -> do
      let groups = Prefix.partitionPrefixesSuffixes chain
      let options = groups |> fmap (fst .> head .> uncurry Prefix.join .> fromJust)
      if length options < 2 then
        return $ Left ["nothing can split"]
      else do
        partition <-
          options
          |> fmap ChainOptionSlot
          |> inputPartition "partition chains to split:"
          |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
        if length partition == 1 then
          return $ Left ["nothing to split"]
        else
          case Prefix.splitMorphism partition bac of
            Nothing -> return $ Left ["fail to split the morphism"]
            Just (bac', updater) ->
              return $ Right $
                workspace { bac = bac' }
                |> updateBufferBy (updater .> return)
    _ -> return $ Left ["should be a non-initial chain"]

splitObjectIncoming :: Control m => Workspace -> m (Either [String] Workspace)
splitObjectIncoming workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperObject chain -> do
      let groups = Prefix.partitionIncoming bac (Prefix.source chain)
      let options = fmap head groups
      if length options < 2 then
        return $ Left ["nothing can split"]
      else do
        partition <-
          options
          |> fmap ChainOptionSlot
          |> inputPartition "partition chains to split:"
          |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
        if length partition == 1 then
          return $ Left ["nothing to split"]
        else do
          strs <- inputTokens bac (length partition)
          case Prefix.splitObjectIncoming (Prefix.source chain) (strs `zip` partition) bac of
            Nothing -> return $ Left ["fail to split the morphism"]
            Just (bac', updater) ->
              return $ Right $
                workspace { bac = bac' }
                |> updateBufferBy updater
    _ -> return $ Left ["should be a node"]

splitObjectOutgoing :: Control m => Workspace -> m (Either [String] Workspace)
splitObjectOutgoing workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperObject chain -> do
      let groups = Prefix.partitionOutgoing (Prefix.source chain)
      let options = fmap head groups
      if length options < 2 then
        return $ Left ["nothing can split"]
      else do
        partition <-
          options
          |> fmap ChainOptionSlot
          |> inputPartition "partition chains to split:"
          |> fmap (fmap (fmap \(ChainOptionSlot c) -> c))
        if length partition == 1 then
          return $ Left ["nothing to split"]
        else do
          strs <- inputTokens bac (length partition)
          case Prefix.splitObjectOutgoing (Prefix.source chain) (strs `zip` partition) bac of
            Nothing -> return $ Left ["fail to split the morphism"]
            Just (bac', updater) ->
              return $ Right $
                workspace { bac = bac' }
                |> updateBufferBy updater
    _ -> return $ Left ["should be a node"]

mergeMorphisms :: Control m => Workspace -> m (Either [String] Workspace)
mergeMorphisms workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperMorphism chain -> do
      let groups = Prefix.findMergableChains bac chain
      let options = groups |> filter ((==~ chain) .> not)
      if null options then
        return $ Left ["nothing can merge"]
      else do
        chain' <-
          options
          |> fmap ChainOptionSlot
          |> inputSelection "select a chain to merge:"
          |> fmap \(ChainOptionSlot c) -> c
        case Prefix.mergeMorphsisms [chain, chain'] bac of
          Nothing -> return $ Left ["fail to merge morphisms"]
          Just (bac', updater) ->
            return $ Right $
              workspace { bac = bac' }
              |> updateBufferBy (updater .> return)
    _ -> return $ Left ["should be a non-initial chain"]

newtype ZipOptionSlot = ZipOptionSlot [(Chain, Chain)]

instance Show ZipOptionSlot where
  show (ZipOptionSlot []) = "(no rule is needed)"
  show (ZipOptionSlot eq) =
    eq
    |> fmap (both (Prefix.getStrings .> concat))
    |> concatMap \(s1, s2) -> s1 ++ " ~ " ++ s2 ++ "; "

mergeObjectsOutgoing :: Control m => Workspace -> m (Either [String] Workspace)
mergeObjectsOutgoing workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperObject chain -> do
      let node = Prefix.source chain
      let groups = Prefix.findIncomingZippableObjects bac node
      let options = groups |> fmap fst |> filter ((==- node) .> not)
      if null options then
        return $ Left ["nothing can merge"]
      else do
        node' <-
          options
          |> fmap (Prefix.id .> ChainOptionSlot)
          |> inputSelection "select a node to merge:"
          |> fmap \(ChainOptionSlot c) -> Prefix.source c
        let incomings = groups |> find (fst .> (==- node)) |> fromJust |> snd |> head
        let options = groups |> find (fst .> (==- node')) |> fromJust |> snd
        incomings' <-
          options
          |> fmap (zip incomings .> ZipOptionSlot)
          |> inputSelection "select a zip strategy:"
          |> fmap \(ZipOptionSlot opt) -> fmap snd opt
        case Prefix.mergeObjectsOutgoing [(node, incomings), (node', incomings')] bac of
          Nothing -> return $ Left ["fail to merge objects"]
          Just (bac', updater) ->
            return $ Right $
              workspace { bac = bac' }
              |> updateBufferBy (updater .> return)
    _ -> return $ Left ["should be a node"]

mergeObjectsIncoming :: Control m => Workspace -> m (Either [String] Workspace)
mergeObjectsIncoming workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperObject chain -> do
      let node = Prefix.source chain
      let groups = Prefix.findOutgoingZippableObjects bac node
      let options = groups |> fmap fst |> filter ((==- node) .> not)
      if null options then
        return $ Left ["nothing can merge"]
      else do
        node' <-
          options
          |> fmap (Prefix.id .> ChainOptionSlot)
          |> inputSelection "select a node to merge:"
          |> fmap \(ChainOptionSlot c) -> Prefix.source c
        let outgoings = groups |> find (fst .> (==- node)) |> fromJust |> snd |> head
        let options = groups |> find (fst .> (==- node')) |> fromJust |> snd
        outgoings' <-
          options
          |> fmap (zip outgoings .> ZipOptionSlot)
          |> inputSelection "select a zip strategy:"
          |> fmap \(ZipOptionSlot opt) -> fmap snd opt
        case Prefix.mergeObjectsIncoming [(node, outgoings), (node', outgoings')] bac of
          Nothing -> return $ Left ["fail to merge objects"]
          Just (bac', updater) ->
            return $ Right $
              workspace { bac = bac' }
              |> updateBufferBy (updater .> return)
    _ -> return $ Left ["should be a node"]

data CofractionOptionSlot = CofractionOptionSlot String (Chain, Chain)

instance Show CofractionOptionSlot where
  show (CofractionOptionSlot str (chain1, chain2)) =
    concat (Prefix.getStrings chain2) ++ " * " ++ str ++ " ~ " ++ concat (Prefix.getStrings chain1)

data FractionOptionSlot = FractionOptionSlot String (Chain, Chain)

instance Show FractionOptionSlot where
  show (FractionOptionSlot str (chain1, chain2)) =
    str ++ " * " ++ concat (Prefix.getStrings chain2) ++ " ~ " ++ concat (Prefix.getStrings chain1)

addMorphism :: Control m => Workspace -> m (Either [String] Workspace)
addMorphism workspace@(Workspace { bac }) =
  case getBuffers workspace of
    [Right chain] | isProperMorphism chain -> do
      go (Prefix.source chain) (Prefix.target chain)
    [Right chain1, Right chain2] | isProperObject chain1 && isProperObject chain2 ->
      let
        node1 = Prefix.source chain1
        node2 = Prefix.source chain2
      in
        if notNull $ fromJust $ Prefix.init bac node2 `Prefix.dividel` Prefix.init bac node1 then
          return $ Left ["invalid node order to add morphism"]
        else
          go node1 node2
    _ -> return $ Left ["should be two nodes or a chain"]
  where
  go node1 node2 =
    case Prefix.getPossibleChainRules bac node1 node2 of
      Nothing ->
        return $ Left ["cannot add a morphism"]
      Just (optionss1, optionss2) -> do
        str <- inputToken bac
        -- TODO: shrink options by compatibleChainRule
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
        if not (Prefix.compatibleChainRule bac (cofractions, fractions)) then
          return $ Left ["invalid rules"]
        else
          case Prefix.addMorphism node1 node2 (cofractions, fractions) str bac of
            Nothing -> return $ Left ["fail to add a morphism"]
            Just (bac', updater) ->
              return $ Right $
                workspace { bac = bac' }
                |> updateBufferBy (updater .> return)
                |> insertResult [Right $ fromJust $ Prefix.fromString bac' str]
