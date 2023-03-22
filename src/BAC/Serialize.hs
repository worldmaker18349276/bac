{-# LANGUAGE BlockArguments #-}

module BAC.Serialize (encodeDict, encodeAsYAMLBy, encodeAsYAML, encodeAsYAML', encodeBy,
  encode, encode', printNode, printNode') where

import BAC.Base hiding (modify)
import Utils.Utils ((|>), (.>))

import Data.List (intercalate)
import Control.Monad.State (State, execState, modify, MonadState (get, put))
import Data.Map (Map, toList, lookup, fromList)
import Data.Foldable (traverse_)
import Prelude hiding (lookup)
import Data.Maybe (fromMaybe)
import Data.Tuple.Extra (both)
import Control.Monad (when)

encodeDict :: Dict -> String
encodeDict =
  toList
  .> fmap (both show)
  .> fmap (\(k, v) -> k ++ "->" ++ v)
  .> intercalate "; "

countStruct :: Arrow e -> State [(Symbol, Int)] ()
countStruct curr =
  extend curr |> traverse_ \arr -> do
    let sym = symbol arr
    state <- get
    let is_new = state |> all (fst .> (/= sym))
    modify $ incre sym
    when is_new $ countStruct arr
  where
  incre :: Eq a => a -> [(a, Int)] -> [(a, Int)]
  incre a [] = [(a, 1)]
  incre a ((a', n) : res) = if a == a' then (a', n+1) : res else (a', n) : incre a res

makePointers :: Enum p => Node e -> p -> Map Symbol p
makePointers node p =
  root node
  |> countStruct
  |> (`execState` mempty)
  |> filter (snd .> (> 1))
  |> fmap fst
  |> (`zip` [p..])
  |> fromList

encodeBy :: (e -> Maybe String) -> Node e -> String
encodeBy showE node =
  root node
  |> format showE 0
  |> (`execState` FormatterState (makePointers node 0) [] "")
  |> output

encode :: Show e => Node e -> String
encode = encodeBy (show .> Just)

encode' :: Node e -> String
encode' = encodeBy (const Nothing)

printNode :: Show e => Node e -> IO ()
printNode = encode .> putStr

printNode' :: Node e -> IO ()
printNode' = encode' .> putStr

encodeAsYAMLBy :: (e -> Maybe String) -> Node e -> String
encodeAsYAMLBy showE node =
  root node
  |> formatYAML showE 0
  |> (`execState` FormatterState (makePointers node 0) [] "")
  |> output

encodeAsYAML :: Show e => Node e -> String
encodeAsYAML = encodeAsYAMLBy (show .> Just)

encodeAsYAML' :: Node e -> String
encodeAsYAML' = encodeAsYAMLBy (const Nothing)

data FormatterState = FormatterState
  {
    pointers :: Map Symbol Int,
    is_init :: [Symbol],
    output :: String
  }

write :: String -> State FormatterState ()
write str = modify (\state -> state {output = output state ++ str})

format :: (e -> Maybe String) -> Int -> Arrow e -> State FormatterState ()
format showE level curr = do
  let indent = repeat " " |> take (level * 2) |> concat

  let sym = symbol curr
  state <- get
  let ptr = lookup sym (pointers state)

  case ptr of
    Just n | sym `elem` is_init state -> do
      write $ indent ++ "*" ++ show n ++ "\n"
    _ -> do
      case ptr of
        Just n -> do
          put $ state { is_init = sym : is_init state }
          write $ indent ++ "&" ++ show n ++ "\n"
        Nothing -> do
          write ""
      edges (target curr) |> traverse_ \(value, arr) -> do
        let value_str = showE value |> fmap (\s -> " (" ++ s ++ ")") |> fromMaybe ""
        write $ indent ++ "- " ++ encodeDict (dict arr) ++ value_str ++ "\n"
        format showE (level + 1) (curr `join` arr)

formatYAML :: (e -> Maybe String) -> Int -> Arrow e -> State FormatterState ()
formatYAML showE level curr =
  edges (target curr) |> traverse_ \(value, arr) -> do
    let indent = repeat " " |> take (level * 4) |> concat

    case showE value of
      Just estr -> do
        write $ indent ++ "- value: " ++ estr ++ "\n"
        write $ indent ++ "  dict: '" ++ encodeDict (dict arr) ++ "'\n"
        write indent
      Nothing -> do
        write $ indent ++ "- dict: '" ++ encodeDict (dict arr) ++ "'\n"
        write indent

    let arr' = curr `join` arr
    let sym = symbol arr'
    state <- get
    let ptr = lookup sym (pointers state)

    case ptr of
      Just n | sym `elem` is_init state ->
        write $ "  target: *" ++ show n
      Just n -> do
        put $ state { is_init = sym : is_init state }
        write $ "  target: &" ++ show n
      Nothing -> do
        write "  target:"

    case ptr of
      Just _ | sym `elem` is_init state -> write "\n"
      _ | null (edges (target arr')) -> write " []\n"
      _ -> do
        write "\n"
        formatYAML showE (level + 1) arr'
