{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main (main) where

import Control.Exception (IOException, catch)
import Control.Monad.Trans.Except (ExceptT (..))
import System.Environment (getArgs)
import Prelude hiding (interact)

import Editor (Editor, openEditor, update)
import Interactive (KeyboardInput, interact)
import Render (renderEditor)
import Utils
import Workspace (FileAccessControl (..))



safeWriteFile :: FilePath -> String -> IO (Either [String] ())
safeWriteFile path contents =
  (Right <$> writeFile path contents) `catch` \(e :: IOException) -> do
    return $ Left ["fail to write file: " ++ path]

safeReadFile :: FilePath -> IO (Either [String] String)
safeReadFile path =
  (Right <$> readFile path) `catch` \(e :: IOException) -> do
    return $ Left ["fail to read file: " ++ path]

newtype FileAccess a = FileAccess (IO a) deriving (Functor, Applicative, Monad)

instance FileAccessControl FileAccess where
  save filepath contents = safeWriteFile filepath contents |> FileAccess |> ExceptT
  open filepath = safeReadFile filepath |> FileAccess |> ExceptT

initialize :: Maybe String -> Maybe String -> IO Editor
initialize bac_path bank_path = do
  let FileAccess m_editor = openEditor bac_path bank_path
  editor <- m_editor
  renderEditor editor
  return editor
  
run :: KeyboardInput -> Editor -> IO (Maybe Editor)
run key editor = do
  let FileAccess m_next_editor = update key editor
  next_editor <- m_next_editor
  renderEditor next_editor
  return $ Just next_editor

main :: IO ()
main = do
  args <- getArgs
  let bac_filepath : bank_filepath : _ = args ++ ["", ""]
  let bac_filepath' = if null bac_filepath then Nothing else Just bac_filepath
  let bank_filepath' = if null bank_filepath then Nothing else Just bank_filepath
  state <- initialize bac_filepath' bank_filepath'
  interact run state
