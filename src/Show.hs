module Show where

import BAC
import Data.List (intercalate)
import Control.Monad.State (State, execState, modify)
import Data.Map (Map, toList)
import Data.Foldable (for_)

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

showStruct :: Node e n -> String
showStruct bac =
  root bac |> showStruct' 0 |> (`execState` FormatterState mempty "") |> output

data FormatterState = FormatterState
  {
    pointers :: Map Symbol Int,
    output :: String
  }

write :: String -> State FormatterState ()
write str = modify (\state -> state {output = output state ++ str})

indent :: Int -> State FormatterState ()
indent level = write $ repeat " " |> take (level * 4) |> concat

showStruct' :: Int -> Arrow () e n -> State FormatterState ()
showStruct' level curr = do
  for_ (edges (node curr)) $ \edge -> do
    indent level
    write "- dict: "
    write $ showDict (dict edge)
    write "\n"
    indent level
    write "  node:\n"
    showStruct' (level + 1) (curr `join` edge)
