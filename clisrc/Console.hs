{-# LANGUAGE NamedFieldPuns #-}
module Console where

import Prefix (PrefixBAC, Node, Chain)
import qualified Prefix
import Data.List.Extra (snoc)
import Data.Maybe (fromJust)

data Cursor = Cursor { line :: Int, column :: Int, columnFrom :: Int }

data ConsoleState = ConsoleState {
  bac :: PrefixBAC,
  buffer :: [Either String Chain],
  memory :: [Either String Chain],
  cursor :: Cursor
}

data Motion =
  MoveUp
  | MoveDown
  | MoveLeft
  | MoveRight
  | DragUp
  | DragDown
  | SelectLeft
  | SelectRight
  | Dup
  | Drop
  | DropTop

getBuffer :: ConsoleState -> Maybe (Either String Chain)
getBuffer (ConsoleState { cursor, buffer, memory })
  | line cursor < length buffer = Just $ buffer !! line cursor
  | line cursor == length buffer = Nothing
  | line cursor < length buffer + 1 + length memory = Just $ memory !! (line cursor - length buffer - 1)
  | otherwise = Nothing

getPart :: (Int, Int) -> Either String Chain -> Either String Chain
getPart (from, to) (Left str) = Left $ drop (min from to) $ take (max from to) str
getPart (from, to) (Right chain) = Right $
  snd $ fromJust $ Prefix.split (min from to) $
  fst $ fromJust $ Prefix.split (max from to) chain

insertAt :: Int -> a -> [a] -> [a]
insertAt 0 a t = a:t
insertAt _ a [] = [a]
insertAt i a (b:t) = b:insertAt (i - 1) a t

removeAt :: Int -> [a] -> [a]
removeAt 0 (_:t) = t
removeAt i (a:t) = a:removeAt (i - 1) t
removeAt _ [] = []

swapNext :: Int -> [a] -> [a]
swapNext 0 (a:b:t) = b:a:t
swapNext i (a:t) = a:swapNext (i - 1) t
swapNext _ t = t

runMotion :: Motion -> ConsoleState -> ConsoleState
runMotion MoveDown state@(ConsoleState { cursor, buffer, memory })
  | line cursor < length buffer + 1 + length memory
  = state { cursor = cursor { line = line cursor + 1, column = 0, columnFrom = 0 } }
  | otherwise
  = state
runMotion MoveUp state@(ConsoleState { cursor, buffer })
  | line cursor > 0
  = state { cursor = cursor { line = line cursor - 1, column = 0, columnFrom = 0 } }
  | null buffer || either length Prefix.length (head buffer) /= 0
  = state { buffer = Left "" : buffer }
  | otherwise
  = state
runMotion MoveRight state@(ConsoleState { cursor }) = case getBuffer state of
  Just (Left str) | column cursor < length str ->
    state { cursor = cursor { column = column cursor + 1, columnFrom = column cursor + 1 } }
  Just (Right chain) | column cursor < Prefix.length chain ->
    state { cursor = cursor { column = column cursor + 1, columnFrom = column cursor + 1 } }
  _ -> state { cursor = cursor { columnFrom = column cursor } }
runMotion MoveLeft state@(ConsoleState { cursor })
  | column cursor > 0
  = state { cursor = cursor { column = column cursor - 1, columnFrom = column cursor - 1 } }
  | otherwise
  = state { cursor = cursor { columnFrom = column cursor } }
runMotion DragDown state@(ConsoleState { cursor, buffer, memory })
  | line cursor < length buffer - 1
  = state { cursor = cursor { line = line cursor + 1 }, buffer = swapNext (line cursor) buffer }
  | line cursor == length buffer - 1
  = state { cursor = cursor { line = line cursor + 1 }, buffer = init buffer, memory = last buffer : memory }
  | line cursor == length buffer
  = state { cursor = cursor { line = line cursor + 1 }, buffer = buffer `snoc` head memory, memory = tail memory }
  | line cursor < length buffer + 1 + length memory - 1
  = state { cursor = cursor { line = line cursor + 1 }, memory = swapNext (line cursor - (length buffer + 1)) memory }
  | otherwise
  = state
runMotion DragUp state@(ConsoleState { cursor, buffer, memory })
  | line cursor == 0
  = state
  | line cursor < length buffer
  = state { cursor = cursor { line = line cursor - 1 }, buffer = swapNext (line cursor - 1) buffer }
  | line cursor == length buffer
  = state { cursor = cursor { line = line cursor - 1 }, buffer = init buffer, memory = last buffer : memory }
  | line cursor == length buffer + 1
  = state { cursor = cursor { line = line cursor - 1 }, buffer = buffer `snoc` head memory, memory = tail memory }
  | otherwise
  = state { cursor = cursor { line = line cursor - 1 }, memory = swapNext (line cursor - (length buffer + 1) - 1) memory }
runMotion SelectRight state@(ConsoleState { cursor }) = case getBuffer state of
  Just (Left str) | column cursor < length str ->
    state { cursor = cursor { column = column cursor + 1 } }
  Just (Right chain) | column cursor < Prefix.length chain ->
    state { cursor = cursor { column = column cursor + 1 } }
  _ -> state
runMotion SelectLeft state@(ConsoleState { cursor })
  | column cursor > 0
  = state { cursor = cursor { column = column cursor - 1 } }
  | otherwise
  = state
runMotion Dup state@(ConsoleState { cursor, buffer, memory })
  | line cursor < length buffer
  = state { buffer = insertAt (line cursor) dup_slot buffer, cursor = dup_cursor }
  | line cursor == length buffer
  = state
  | otherwise
  = state { memory = insertAt (line cursor - (length buffer + 1)) dup_slot memory, cursor = dup_cursor }
  where
  slot = fromJust $ getBuffer state
  dup_slot =
    if column cursor == columnFrom cursor then slot
    else getPart (column cursor, columnFrom cursor) slot
  dup_cursor =
    if column cursor == columnFrom cursor then cursor
    else cursor {
      column = column cursor - min (column cursor) (columnFrom cursor),
      columnFrom = columnFrom cursor - min (column cursor) (columnFrom cursor)
    }
runMotion Drop state@(ConsoleState { cursor, buffer, memory })
  | line cursor < length buffer
  = state { buffer = removeAt (line cursor) buffer, cursor = cursor { column = 0, columnFrom = 0 } }
  | line cursor == length buffer
  = state
  | otherwise
  = state { memory = removeAt (line cursor - (length buffer + 1)) memory, cursor = cursor { column = 0, columnFrom = 0 } }
runMotion DropTop state@(ConsoleState { cursor, buffer })
  | line cursor < length buffer
  = state { buffer = [], cursor = cursor { line = 0, column = 0, columnFrom = 0 } }
  | otherwise
  = state { buffer = [], cursor = cursor { line = line cursor - length buffer } }



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
