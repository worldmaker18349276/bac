{-# LANGUAGE BlockArguments #-}

module BAC.Serialize (
  encodeDict,
  encodeAsYAML,
  encode,
  printNode,
) where

import BAC.Base hiding (modify)
import Utils.Utils ((|>), (.>))

import Data.List (intercalate)
import Control.Monad.State (State, execState, modify, MonadState (get, put))
import Data.Map (Map, toList, lookup, fromList)
import Data.Foldable (traverse_)
import Prelude hiding (lookup)
import Data.Tuple.Extra (both)
import Control.Monad (when)

encodeDict :: Dict -> String
encodeDict =
  toList
  .> fmap (both show)
  .> fmap (\(k, v) -> k ++ "->" ++ v)
  .> intercalate "; "

countStruct :: Arrow -> State [(Symbol, Int)] ()
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

makePointers :: Enum p => Node -> p -> Map Symbol p
makePointers node p =
  root node
  |> countStruct
  |> (`execState` mempty)
  |> filter (snd .> (> 1))
  |> fmap fst
  |> (`zip` [p..])
  |> fromList

encode :: Node -> String
encode node =
  root node
  |> format 0
  |> (`execState` FormatterState (makePointers node 0) [] "")
  |> output

printNode :: Node -> IO ()
printNode = encode .> putStr

encodeAsYAML :: Node -> String
encodeAsYAML node =
  root node
  |> formatYAML 0
  |> (`execState` FormatterState (makePointers node 0) [] "")
  |> output

data FormatterState = FormatterState
  {
    pointers :: Map Symbol Int,
    is_init :: [Symbol],
    output :: String
  }

write :: String -> State FormatterState ()
write str = modify (\state -> state {output = output state ++ str})

format :: Int -> Arrow -> State FormatterState ()
format level curr = do
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
      edges (target curr) |> traverse_ \edge -> do
        write $ indent ++ "- " ++ encodeDict (dict edge) ++ "\n"
        format (level + 1) (curr `join` edge)

formatYAML :: Int -> Arrow -> State FormatterState ()
formatYAML level curr =
  edges (target curr) |> traverse_ \edge -> do
    let indent = repeat " " |> take (level * 4) |> concat

    write $ indent ++ "- dict: '" ++ encodeDict (dict edge) ++ "'\n"
    write indent

    let arr = curr `join` edge
    let sym = symbol arr
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
      _ | null (edges (target arr)) -> write " []\n"
      _ -> do
        write "\n"
        formatYAML (level + 1) arr
