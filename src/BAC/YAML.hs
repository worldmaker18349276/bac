{-# LANGUAGE BlockArguments #-}

module BAC.YAML (encodeDict, encodeNode, encodeNodeBy, encodeNode') where

import BAC.Base hiding (modify)
import Utils.Utils ((|>), (.>), both)

import Data.List (intercalate)
import Control.Monad.State (State, execState, modify, MonadState (get, put))
import Data.Map (Map, toList, lookup, fromList, unionWith)
import Data.Foldable (traverse_)
import Data.Monoid (Sum)
import Prelude hiding (lookup)
import Data.Maybe (isNothing)
import Control.Monad (when)

encodeDict :: Dict -> String
encodeDict =
  toList
  .> fmap (both show)
  .> fmap (\(k, v) -> k ++ "->" ++ v)
  .> intercalate "; "
  .> ("{" ++)
  .> (++ "}")

countStruct :: Arrow e -> State (Map Symbol (Sum Int)) ()
countStruct curr =
  next curr |> traverse_ \arr -> do
    let sym = symbolize arr
    state <- get
    let is_new = isNothing (lookup sym state)
    modify $ unionWith (<>) (fromList [(sym, 1)])
    when is_new $ countStruct arr

encodeNodeBy :: (e -> Maybe String) -> Node e -> String
encodeNodeBy showE bac =
  root bac
  |> format showE 0
  |> (`execState` FormatterState ptrs [] "")
  |> output
  where
  ptrs =
    root bac
    |> countStruct
    |> (`execState` mempty)
    |> toList
    |> filter (snd .> (> 1))
    |> fmap fst
    |> (`zip` [0..])
    |> fromList

encodeNode :: Show e => Node e -> String
encodeNode = encodeNodeBy (show .> Just)

encodeNode' :: Node e -> String
encodeNode' = encodeNodeBy (const Nothing)

data FormatterState = FormatterState
  {
    pointers :: Map Symbol Int,
    is_init :: [Symbol],
    output :: String
  }

write :: String -> State FormatterState ()
write str = modify (\state -> state {output = output state ++ str})

indent :: Int -> State FormatterState ()
indent level = write $ repeat " " |> take (level * 4) |> concat

format :: (e -> Maybe String) -> Int -> Arrow e -> State FormatterState ()
format showE level curr =
  edges (node curr) |> traverse_ \edge -> do
    case showE (value edge) of
      Just estr -> do
        indent level
        write $ "- value: " ++ estr ++ "\n"
        indent level
        write $ "  dict: " ++ encodeDict (dict edge) ++ "\n"
        indent level
      Nothing -> do
        indent level
        write $ "- dict: " ++ encodeDict (dict edge) ++ "\n"
        indent level

    let arr = curr `join` edge
    let sym = symbolize arr
    state <- get
    let ptr = lookup sym (pointers state)

    case ptr of
      Just n | sym `elem` is_init state ->
        write $ "  node: *" ++ show n
      Just n -> do
        put $ state { is_init = sym : is_init state }
        write $ "  node: &" ++ show n
      Nothing -> do
        write "  node:"

    case ptr of
      Just _ | sym `elem` is_init state -> write "\n"
      _ | null (edges (node arr)) -> write " []\n"
      _ -> do
        write "\n"
        format showE (level + 1) arr
