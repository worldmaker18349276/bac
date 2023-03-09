module Show (showSymbol, showDict, showStruct) where

import BAC
import Data.List (intercalate)
import Control.Monad.State (State, execState, modify, MonadState (get, put))
import Data.Map (Map, toList, lookup, fromList, unionWith)
import Data.Foldable (for_)
import Data.Monoid (Sum)
import Prelude hiding (lookup)
import Data.Maybe (isNothing)
import Control.Monad (when)

showSymbol :: Symbol -> String
showSymbol (Symbol nums) = nums |> fmap show |> intercalate "." |> ("#" ++)

showDict :: Dict -> String
showDict =
  toList
  .> fmap (both showSymbol)
  .> fmap (\(k, v) -> k ++ "=" ++ v)
  .> intercalate "; "
  .> ("'" ++)
  .> (++ "'")

countStruct :: Arrow () e -> State (Map Symbol (Sum Int)) ()
countStruct curr =
  for_ (next curr) $ \arr -> do
    let sym = symbolize arr
    state <- get
    let is_new = isNothing (lookup sym state)
    modify $ unionWith (<>) (fromList [(sym, 1)])
    when is_new $ countStruct arr

showStruct :: Node e -> String
showStruct bac =
  root bac |> showStruct' 0 |> (`execState` FormatterState ptrs [] "") |> output
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

showStruct' :: Int -> Arrow () e -> State FormatterState ()
showStruct' level curr =
  for_ (edges (node curr)) $ \edge -> do
    indent level
    write $ "- dict: " ++ showDict (dict edge) ++ "\n"
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
        showStruct' (level + 1) arr
