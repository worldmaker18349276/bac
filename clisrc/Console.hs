{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Console where

import Prefix (PrefixBAC, Node, Chain)
import qualified Prefix
import Data.List.Extra (snoc)
import Data.Maybe (fromJust)
import Data.Function ((&))
import Data.Either (isLeft, isRight)
import Data.Char (isPrint)

data Cursor = Cursor { line :: Int, column :: Int, lineFrom :: Int, columnFrom :: Int }

data ConsoleState = ConsoleState {
  bac :: PrefixBAC,
  buffer :: [Either String Chain],
  cursor :: Cursor
}

cursorAt :: Int -> Int -> Cursor
cursorAt line column = Cursor line column line column

selectLines :: ConsoleState -> Int -> Int -> Cursor
selectLines state line_from line_to =
  if line_from <= line_to then
    Cursor line_to (slotLength (buffer state !! line_to)) line_from 0
  else
    Cursor line_to 0 line_from (slotLength (buffer state !! line_from))

slotLength :: Either String Chain -> Int
slotLength (Left str) = length str
slotLength (Right chain) = Prefix.length chain

data Action =
  MoveUp
  | MoveDown
  | MoveLeft
  | MoveRight
  | DragUp
  | DragDown
  | SelectUp
  | SelectDown
  | SelectLeft
  | SelectRight
  | Dup
  | NewSlot
  | Join
  | Input String
  | DeleteBackward
  | DeleteSlot
  | ChangeType
  | InitialChain
  | IsNondecomposable
  | AreSameMorphism
  | AreUnsplittable
  -- | DivideLeft
  -- | DivideRight
  -- | SwingLeft
  -- | SwingRight
  deriving Show

-- data ComplexAction =
--   Search
--   | AddEdge
--   | RemoveEdge
--   | AlterEdge
--   | RemoveMorphism
--   | RemoveObject
--   | AddMorphism
--   | AddObject
--   | InterpolateObject
--   | SplitMorphism
--   | SplitObjectOutgoing
--   | SplitObjectIncoming
--   | MergeMorphisms
--   | MergeObjectsOutgoing
--   | MergeObjectsIncoming

-- data Control m = Control {
--   message :: String -> m (),
--   inputString :: String -> m String,
--   inputSelection :: [String] -> m Int,
--   inputChain :: Chain -> m Chain,
--   inputNode :: Node -> m Node
-- }

-- data Output =
--   OutputString String
--   | OutputChains [Chain]
--   | OutputNodes [Node]

getBuffers :: ConsoleState -> [Either String Chain]
getBuffers (ConsoleState { cursor, buffer }) =
  buffer
  & take (max (line cursor) (lineFrom cursor) + 1)
  & drop (min (line cursor) (lineFrom cursor))

getBuffer :: ConsoleState -> Either String Chain
getBuffer (ConsoleState { cursor, buffer }) = buffer !! line cursor

getPart :: ConsoleState -> Maybe (Either String Chain)
getPart state@(ConsoleState { cursor })
  | line cursor /= lineFrom cursor = Nothing
  | otherwise = case getBuffer state of
    Left str -> str & take (max from to) & drop (min from to) & Left & Just
    Right chain ->
      chain
      & Prefix.split (max from to) & fromJust & fst
      & Prefix.split (min from to) & fromJust & snd
      & Right
      & Just
  where
  from = columnFrom cursor
  to = column cursor

runAction :: Action -> ConsoleState -> Either [String] ConsoleState
runAction MoveDown state@(ConsoleState { cursor, buffer })
  | line cursor < length buffer - 1
  = return state { cursor = cursorAt (line cursor + 1) 0 }
  | otherwise
  = return state { cursor = cursorAt (line cursor) 0 }
runAction MoveUp state@(ConsoleState { cursor, buffer })
  | line cursor > 0
  = return state { cursor = cursorAt (line cursor - 1) 0 }
  | otherwise
  = return state { cursor = cursorAt (line cursor) 0 }
runAction MoveRight state@(ConsoleState { cursor, buffer })
  | column cursor < slotLength (buffer !! line cursor)
  = return state { cursor = cursorAt (line cursor) (column cursor + 1) }
  | otherwise
  = return state { cursor = cursorAt (line cursor) (column cursor) }
runAction MoveLeft state@(ConsoleState { cursor })
  | column cursor > 0
  = return state { cursor = cursorAt (line cursor) (column cursor - 1) }
  | otherwise
  = return state { cursor = cursorAt (line cursor) (column cursor) }
runAction DragDown state@(ConsoleState { cursor, buffer })
  | to < length buffer
  = return state {
      cursor = cursor { line = line cursor + 1, lineFrom = lineFrom cursor + 1 },
      buffer = take from buffer ++ [buffer !! to] ++ drop from (take to buffer) ++ drop (to + 1) buffer
      }
  | otherwise
  = return state
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
runAction DragUp state@(ConsoleState { cursor, buffer })
  | from > 0
  = return state {
      cursor = cursor { line = line cursor - 1, lineFrom = lineFrom cursor - 1 },
      buffer = take (from - 1) buffer ++ drop from (take to buffer) ++ [buffer !! (from - 1)] ++ drop to buffer
      }
  | otherwise
  = return state
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
runAction SelectDown state@(ConsoleState { cursor, buffer })
  | line cursor < length buffer - 1
  = return state { cursor = selectLines state (lineFrom cursor) (line cursor + 1) }
  | otherwise
  = return state { cursor = selectLines state (lineFrom cursor) (line cursor) }
runAction SelectUp state@(ConsoleState { cursor, buffer })
  | line cursor > 0
  = return state { cursor = selectLines state (lineFrom cursor) (line cursor - 1) }
  | otherwise
  = return state { cursor = selectLines state (lineFrom cursor) (line cursor) }
runAction SelectRight state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor
  = return state
  | column cursor < slotLength (buffer !! line cursor)
  = return state { cursor = cursor { column = column cursor + 1 } }
  | otherwise
  = return state
runAction SelectLeft state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor
  = return state
  | column cursor > 0
  = return state { cursor = cursor { column = column cursor - 1 } }
  | otherwise
  = return state
runAction Dup state@(ConsoleState { cursor, buffer }) =
  let
    dup_slots =
      if line cursor == lineFrom cursor && column cursor == columnFrom cursor then
        [buffer !! line cursor]
      else
        maybe (getBuffers state) (: []) (getPart state)
    dup_line = max (line cursor) (lineFrom cursor) + 1
    shift_line = abs (line cursor - lineFrom cursor) + 1
    dup_cursor
      | line cursor == lineFrom cursor && column cursor > columnFrom cursor
      = Cursor (line cursor + shift_line) (slotLength (head dup_slots)) (lineFrom cursor + shift_line) 0
      | line cursor == lineFrom cursor && column cursor < columnFrom cursor
      = Cursor (line cursor + shift_line) 0 (lineFrom cursor + shift_line) (slotLength (head dup_slots))
      | otherwise
      = cursor { line = line cursor + shift_line, lineFrom = lineFrom cursor + shift_line }
  in
    Right state { buffer = take dup_line buffer ++ dup_slots ++ drop dup_line buffer, cursor = dup_cursor }
runAction NewSlot state@(ConsoleState { cursor, buffer })
  = return state { buffer = take line' buffer ++ [Left ""] ++ drop line' buffer, cursor = cursorAt line' 0 }
  where
  line' = max (line cursor) (lineFrom cursor) + 1
runAction Join state@(ConsoleState { cursor, buffer })
  | all isLeft buffer'
  = return state {
    buffer = take from buffer ++ [Left $ concatMap (\(Left a) -> a) buffer'] ++ drop to buffer,
    cursor = cursorAt from 0
    }
  | all isRight buffer'
  = case join_chain of
    Just join_chain ->
      return state {
        buffer = take from buffer ++ [Right join_chain] ++ drop to buffer,
        cursor = cursorAt from 0
        }
    Nothing -> Left ["cannot join those chains"]
  | otherwise
  = Left ["cannot join strings and chains"]
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  buffer' = drop from (take to buffer)
  join_chain =
    buffer'
    & fmap (\(Right chain) -> Just chain)
    & foldl1 \a b -> do
      a <- a
      b <- b
      Prefix.concat a b
runAction (Input str) state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor
  = Left ["should on a single line"]
  | isRight (buffer !! line cursor)
  = Left ["should be a string"]
  | not (all isPrint str)
  = Left ["cannot input non-printable character"]
  | otherwise
  = return state {
    buffer = take (line cursor) buffer ++ [Left res] ++ drop (line cursor + 1) buffer,
    cursor = cursorAt (line cursor) col
    }
  where
  Left str' = buffer !! line cursor
  from = min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
  res = take from str' ++ str ++ drop to str'
  col = from + length str
runAction DeleteBackward state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor || slotLength (buffer !! line cursor) == 0
  = let
      line' = min (line cursor) (lineFrom cursor) - 1
      cursor' = if line' < 0 then cursorAt 0 0 else cursorAt line' (slotLength (buffer !! line'))
    in
      return state {
        buffer = replace_buffer [],
        cursor = cursor'
        }
  | otherwise
  = case buffer !! line cursor of
    Left str ->
      return state {
        buffer = replace_buffer [Left $ take from str ++ drop to str],
        cursor = cursorAt (line cursor) from
        }
    Right chain | from == 0 && to == Prefix.length chain && column cursor < columnFrom cursor ->
      return state {
        buffer = replace_buffer [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
        }
    Right chain | from == 0 && to == Prefix.length chain && column cursor > columnFrom cursor ->
      return state {
        buffer = replace_buffer [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
        }
    Right chain | to == Prefix.length chain ->
      return state {
        buffer = replace_buffer [Right $ fst $ fromJust $ Prefix.split from chain],
        cursor = cursorAt (line cursor) from
        }
    Right chain | from == 0 ->
      return state {
        buffer = replace_buffer [Right $ snd $ fromJust $ Prefix.split to chain],
        cursor = cursorAt (line cursor) from
        }
    Right chain ->
      Left ["can only delete end of chains"]
  where
  replace_buffer slots = if null buffer' then [Left ""] else buffer'
    where
    from = min (line cursor) (lineFrom cursor)
    to = max (line cursor) (lineFrom cursor) + 1
    buffer' = take from buffer ++ slots ++ drop to buffer
  from = if column cursor == columnFrom cursor && column cursor /= 0 then
      column cursor - 1
    else
      min (column cursor) (columnFrom cursor)
  to = max (column cursor) (columnFrom cursor)
runAction DeleteSlot state@(ConsoleState { cursor, buffer })
  = return state { buffer = if null buffer' then [Left ""] else buffer', cursor = cursorAt line' 0 }
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  line' = max (from - 1) 0
  buffer' = take from buffer ++ drop to buffer
runAction ChangeType state@(ConsoleState { bac, cursor, buffer })
  | line cursor /= lineFrom cursor
  = Left ["should on a single line"]
  | otherwise
  = case buffer !! line cursor of 
    Right chain ->
      return state {
        buffer = replace_buffer (Left $ concat $ Prefix.getStrings chain),
        cursor = cursorAt (line cursor) 0
        }
    Left str | null str ->
        return state {
          buffer = replace_buffer (Right $ Prefix.id $ Prefix.root bac),
          cursor = cursorAt (line cursor) 0
          }
    Left str -> case Prefix.fromString bac str of
      Nothing -> Left ["not a valid chain"]
      Just chain -> 
        return state {
          buffer = replace_buffer (Right chain),
          cursor = cursorAt (line cursor) 0
          }
  where
  replace_buffer slot = take (line cursor) buffer ++ [slot] ++ drop (line cursor + 1) buffer
runAction InitialChain state@(ConsoleState { bac, cursor, buffer })
  | line cursor /= lineFrom cursor
  = Left ["should on a single line"]
  | isLeft $ buffer !! line cursor
  = Left ["should be a chain"]
  | slotLength (buffer !! line cursor) /= 0
  = Left ["not a null chain"]
  | otherwise
  = return state {
    buffer = replace_buffer (Right init_chain),
    cursor = cursorAt (line cursor) (Prefix.length init_chain)
    }
  where
  replace_buffer slot = take (line cursor) buffer ++ [slot] ++ drop (line cursor + 1) buffer
  pretoken = Prefix.getPreString $ (\(Right chain) -> chain) $ buffer !! line cursor
  init_chain = if null pretoken then Prefix.id (Prefix.root bac) else fromJust (Prefix.fromString bac pretoken)
runAction IsNondecomposable state@(ConsoleState { bac, cursor, buffer })
  | line cursor /= lineFrom cursor
  = Left ["not a single line"]
  | otherwise
  = case buffer !! line cursor of
    Left _ -> Left ["not a chain"]
    Right chain -> Left [show $ Prefix.isNondecomposable chain]
runAction AreSameMorphism state@(ConsoleState { bac, cursor, buffer })
  | not (all isRight $ drop from (take to buffer))
  = Left ["should be chains"]
  | otherwise
  = Left [show $ allSameBy (Prefix.==~) $ fmap (\(Right chain) -> chain) $ drop from (take to buffer)]
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
runAction AreUnsplittable state@(ConsoleState { bac, cursor, buffer })
  | not (all isRight $ drop from (take to buffer))
  = Left ["should be chains"]
  | otherwise
  = Left [show $ allSameBy Prefix.isUnsplittable $ fmap (\(Right chain) -> chain) $ drop from (take to buffer)]
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1

allSameBy :: (a -> a -> Bool) -> [a] -> Bool
allSameBy _ [] = True
allSameBy f (a:t) = all (f a) t
