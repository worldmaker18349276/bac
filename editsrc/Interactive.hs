{-# LANGUAGE InstanceSigs #-}
{-# HLINT ignore "Use forM_" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Interactive (Key (..), KeyboardInput (..), interact) where

import Data.Char (isPrint)
import System.IO (BufferMode (NoBuffering), hReady, hSetBuffering, hSetEcho, stdin, hFlush, stdout)
import Prelude hiding (Left, Right, interact)
import Data.Either.Extra (maybeToEither)

getKeyCode :: IO String
getKeyCode = reverse <$> getKeyCode' ""
  where
  getKeyCode' chars = do
    char <- getChar
    more <- hReady stdin
    (if more then getKeyCode' else return) (char:chars)

data Key =
  Char Char
  | Up | Down | Left | Right
  | Home | End | PageUp | PageDown
  | Enter | Backspace | Tab | Esc
  | Delete | Insert

instance Show Key where
  show :: Key -> String
  show Up = "Up"
  show Down = "Down"
  show Left = "Left"
  show Right = "Right"
  show Home = "Home"
  show End = "End"
  show PageUp = "PageUp"
  show PageDown = "PageDown"
  show Enter = "Enter"
  show Backspace = "Backspace"
  show Tab = "Tab"
  show Esc = "Esc"
  show Delete = "Delete"
  show Insert = "Insert"
  show (Char ' ') = "Space"
  show (Char ch) = if isPrint ch then [ch] else "<" ++ show ch ++ ">"

data KeyboardInput =
  ModifiedKey Bool Bool Bool Key -- shift alt ctrl key
  | UnrecognizedInput String

instance Show KeyboardInput where
  show :: KeyboardInput -> String
  show (ModifiedKey shift alt ctrl key) =
    (if shift then "Shift-" else "")
    ++ (if alt then "Alt-" else "")
    ++ (if ctrl then "Ctrl-" else "")
    ++ show key
  show (UnrecognizedInput code) = "<" ++ show code ++ ">"

decode :: String -> KeyboardInput
decode ['\ESC', '[', c] | c `elem` "ABCDHF" =
  ModifiedKey False False False key
  where
  key = case c of
    'A' -> Up
    'B' -> Down
    'C' -> Right
    'D' -> Left
    'H' -> Home
    'F' -> End
    _ -> error "unreachable"
decode ['\ESC', '[', '1', ';', n, c] | n `elem` "2345678" && c `elem` "ABCDHF" =
  ModifiedKey shift alt ctrl key
  where
  key = case c of
    'A' -> Up
    'B' -> Down
    'C' -> Right
    'D' -> Left
    'H' -> Home
    'F' -> End
    _ -> error "unreachable"
  m = (read [n] :: Int) - 1
  shift = m `mod` 2 == 1
  alt = (m `div` 2) `mod` 2 == 1
  ctrl = (m `div` 4) `mod` 2 == 1
decode ['\ESC', '[', c, '~'] | c `elem` "2356" =
  ModifiedKey False False False key
  where
  key = case c of
    '2' -> Insert
    '3' -> Delete
    '5' -> PageUp
    '6' -> PageDown
    _ -> error "unreachable"
decode ['\ESC', '[', c, ';', n, '~'] | n `elem` "2345678" && c `elem` "2356" =
  ModifiedKey shift alt ctrl key
  where
  key = case c of
    '2' -> Insert
    '3' -> Delete
    '5' -> PageUp
    '6' -> PageDown
    _ -> error "unreachable"
  m = (read [n] :: Int) - 1
  shift = m `mod` 2 == 1
  alt = (m `div` 2) `mod` 2 == 1
  ctrl = (m `div` 4) `mod` 2 == 1

decode "\n"         = ModifiedKey False False False Enter
decode "\ESC\n"     = ModifiedKey False True  False Enter
decode "\ESC"       = ModifiedKey False False False Esc
decode "\ESC\ESC"   = ModifiedKey False True  False Esc
decode "\t"         = ModifiedKey False False False Tab
decode "\ESC\t"     = ModifiedKey False True  False Tab
decode "\ESC[Z"     = ModifiedKey True  False False Tab -- ShiftTab
decode "\ESC\ESC[Z" = ModifiedKey True  True  False Tab -- ShiftTab
decode "\DEL"       = ModifiedKey False False False Backspace
decode "\ESC\DEL"   = ModifiedKey False True  False Backspace
decode "\b"         = ModifiedKey False False True  Backspace -- CtrlBackspace
decode "\ESC\b"     = ModifiedKey False True  True  Backspace -- CtrlBackspace

decode [ch] | isPrint ch = ModifiedKey False False False (Char ch)
decode ['\ESC', ch] | isPrint ch = ModifiedKey False True False (Char ch)
decode code = UnrecognizedInput code

interact :: (KeyboardInput -> a -> IO (Maybe a)) -> a -> IO ()
interact act init_state = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  hFlush stdout
  go init_state
  where
  go state = do
    code <- getKeyCode
    next_state <- act (decode code) state
    hFlush stdout
    case next_state of
      Nothing -> return ()
      Just next_state -> go next_state
