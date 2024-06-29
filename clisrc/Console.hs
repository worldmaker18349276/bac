{-# LANGUAGE NamedFieldPuns #-}
module Console where

import Prefix (PrefixBAC, Node, Chain)
import qualified Prefix
import Data.List.Extra (snoc)
import Data.Maybe (fromJust)
import Data.Function ((&))

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
  | Drop
  deriving Show

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

runAction :: Action -> ConsoleState -> ConsoleState
runAction MoveDown state@(ConsoleState { cursor, buffer })
  | line cursor < length buffer - 1
  = state { cursor = cursorAt (line cursor + 1) 0 }
  | otherwise
  = state { cursor = cursorAt (line cursor) (length (last buffer)) }
runAction MoveUp state@(ConsoleState { cursor, buffer })
  | line cursor > 0
  = state { cursor = cursorAt (line cursor - 1) 0 }
  | otherwise
  = state { cursor = cursorAt (line cursor) 0 }
runAction MoveRight state@(ConsoleState { cursor, buffer })
  | column cursor < slotLength (buffer !! line cursor)
  = state { cursor = cursorAt (line cursor) (column cursor + 1) }
  | otherwise
  = state { cursor = cursorAt (line cursor) (column cursor) }
runAction MoveLeft state@(ConsoleState { cursor })
  | column cursor > 0
  = state { cursor = cursorAt (line cursor) (column cursor - 1) }
  | otherwise
  = state { cursor = cursorAt (line cursor) (column cursor) }
runAction DragDown state@(ConsoleState { cursor, buffer })
  | to < length buffer
  = state {
      cursor = cursor { line = line cursor + 1, lineFrom = lineFrom cursor + 1 },
      buffer = take from buffer ++ [buffer !! to] ++ drop from (take to buffer) ++ drop (to + 1) buffer
      }
  | otherwise
  = state
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
runAction DragUp state@(ConsoleState { cursor, buffer })
  | from > 0
  = state {
      cursor = cursor { line = line cursor - 1, lineFrom = lineFrom cursor - 1 },
      buffer = take (from - 1) buffer ++ drop from (take to buffer) ++ [buffer !! (from - 1)] ++ drop to buffer
      }
  | otherwise
  = state
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
runAction SelectDown state@(ConsoleState { cursor, buffer })
  | line cursor < length buffer - 1
  = state { cursor = selectLines state (lineFrom cursor) (line cursor + 1) }
  | otherwise
  = state { cursor = selectLines state (lineFrom cursor) (line cursor) }
runAction SelectUp state@(ConsoleState { cursor, buffer })
  | line cursor > 0
  = state { cursor = selectLines state (lineFrom cursor) (line cursor - 1) }
  | otherwise
  = state { cursor = selectLines state (lineFrom cursor) (line cursor) }
runAction SelectRight state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor
  = state
  | column cursor < slotLength (buffer !! line cursor)
  = state { cursor = cursor { column = column cursor + 1 } }
  | otherwise
  = state
runAction SelectLeft state@(ConsoleState { cursor, buffer })
  | line cursor /= lineFrom cursor
  = state
  | column cursor > 0
  = state { cursor = cursor { column = column cursor - 1 } }
  | otherwise
  = state
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
    state { buffer = take dup_line buffer ++ dup_slots ++ drop dup_line buffer, cursor = dup_cursor }
runAction Drop state@(ConsoleState { cursor, buffer })
  = state { buffer = if null buffer' then [Left ""] else buffer', cursor = cursorAt line' 0 }
  where
  from = min (line cursor) (lineFrom cursor)
  to = max (line cursor) (lineFrom cursor) + 1
  line' = max (from - 1) 0
  buffer' = take from buffer ++ drop to buffer



data Control m = Control {
  message :: String -> m (),
  inputString :: String -> m String,
  inputSelection :: [String] -> m Int,
  inputChain :: Chain -> m Chain,
  inputNode :: Node -> m Node
}

data Output =
  OutputString String
  | OutputChains [Chain]
  | OutputNodes [Node]

-- type Action m = Control m -> StateT ConsoleState m Output

-- data Exploration =
--   Search
--   | GetChain
--   | GetRoot
--   | GetSource
--   | GetTarget
--   | TrimLeft
--   | TrimRight
--   | GetId
--   | GetInit
--   | GetOutgoing
--   | GetIncoming
--   | Concat
--   | Split
--   | DivideLeft
--   | DivideRight
--   | IsEqual
--   | IsUnsplittable
--   | IsSameMorphism
--   | IsNondecomposable
--   | Swing
--   | PrefixSwing
--   | SuffixSwing

-- data Modification =
--   AddEdge
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
