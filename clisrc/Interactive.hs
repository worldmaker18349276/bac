{-# HLINT ignore "Use forM_" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}

module Interactive (Key (..), ModifiedKey (..), interact) where

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

data ModifiedKey = ModifiedKey {
    shift :: Bool,
    alt :: Bool,
    ctrl :: Bool,
    key :: Key
  }

instance Show ModifiedKey where
  show :: ModifiedKey -> String
  show (ModifiedKey { shift, alt, ctrl, key }) =
    (if shift then "Shift-" else "")
    ++ (if alt then "Alt-" else "")
    ++ (if ctrl then "Ctrl-" else "")
    ++ show key

decode :: String -> Maybe ModifiedKey
decode ['\ESC', '[', c] | c `elem` "ABCDHF" =
  Just $ ModifiedKey False False False key
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
  Just $ ModifiedKey shift alt ctrl key
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
  Just $ ModifiedKey False False False key
  where
  key = case c of
    '2' -> Insert
    '3' -> Delete
    '5' -> PageUp
    '6' -> PageDown
    _ -> error "unreachable"
decode ['\ESC', '[', c, ';', n, '~'] | n `elem` "2345678" && c `elem` "2356" =
  Just $ ModifiedKey shift alt ctrl key
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

decode "\n"         = Just $ ModifiedKey False False False Enter
decode "\ESC\n"     = Just $ ModifiedKey False True  False Enter
decode "\ESC"       = Just $ ModifiedKey False False False Esc
decode "\ESC\ESC"   = Just $ ModifiedKey False True  False Esc
decode "\t"         = Just $ ModifiedKey False False False Tab
decode "\ESC\t"     = Just $ ModifiedKey False True  False Tab
decode "\ESC[Z"     = Just $ ModifiedKey True  False False Tab -- ShiftTab
decode "\ESC\ESC[Z" = Just $ ModifiedKey True  True  False Tab -- ShiftTab
decode "\DEL"       = Just $ ModifiedKey False False False Backspace
decode "\ESC\DEL"   = Just $ ModifiedKey False True  False Backspace
decode "\b"         = Just $ ModifiedKey False False True  Backspace -- CtrlBackspace
decode "\ESC\b"     = Just $ ModifiedKey False True  True  Backspace -- CtrlBackspace

decode [ch] | isPrint ch = Just $ ModifiedKey False False False (Char ch)
decode ['\ESC', ch] | isPrint ch = Just $ ModifiedKey False True False (Char ch)
decode _ = Nothing

interact :: (Either String ModifiedKey -> a -> IO (Maybe a)) -> a -> IO ()
interact act init_state = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  go init_state
  where
  go state = do
    code <- getKeyCode
    let key = maybeToEither code (decode code)
    next_state <- act key state
    hFlush stdout
    case next_state of
      Nothing -> return ()
      Just next_state -> go next_state
