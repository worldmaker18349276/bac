module Main (main) where

import System.Environment (getArgs)
import Editor (edit)

main :: IO ()
main = do
  args <- getArgs
  let bac_path : strs_path : _ = args ++ ["", ""]
  edit bac_path strs_path
