{-# LANGUAGE BlockArguments #-}

module BAC.Serialize (encodeDict, encodeAsYAML, encode, printBAC) where

import Control.Monad (when)
import Control.Monad.State (MonadState (get), State, execState, modify)
import Data.Foldable (traverse_)
import Data.List (intercalate)
import Data.Map (Map, fromList, lookup, toList)
import Data.Tuple.Extra (both)
import Prelude hiding (lookup)

import BAC.Base hiding (modify)
import Utils.Utils ((.>), (|>))

-- | Encode dictionary as a string concisely.
encodeDict :: Dict -> String
encodeDict =
  toList
  .> fmap (both show)
  .> fmap (\(k, v) -> k ++ "->" ++ v)
  .> intercalate "; "

-- | Count the number of shown references.
countRef :: Arrow -> [(Symbol, Int)]
countRef = go .> (`execState` mempty)
  where
  go = extend .> traverse_ \arr -> do
    let sym = symbol arr
    state <- get
    let is_new = state |> all (fst .> (/= sym))
    modify $ incre sym
    when is_new $ go arr
  incre :: Eq a => a -> [(a, Int)] -> [(a, Int)]
  incre a [] = [(a, 1)]
  incre a ((a', n) : rest) = if a == a' then (a', n+1) : rest else (a', n) : incre a rest

-- | Assign pointers to multi-referenced symbols.
makePointers :: Enum p => p -> BAC -> Map Symbol p
makePointers p =
  root
  .> countRef
  .> filter (snd .> (> 1))
  .> fmap fst
  .> (`zip` [p..])
  .> fromList

{- |
Encode a BAC into a YAML-like string.

For example:

>>> import BAC.Examples
>>> putStr $ encode cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->2; 2->3
    *1

Indentation define block, which represents a node.  A block is consist of a list, whose
items (start with dash) represent edges of this node.  The string after dash is the
dictionary of this edge, and the following indented block is the target of this edge.  The
notations `&n` and `*n` at the first line of a block are referencing and dereferencing of
blocks, indicating implicitly shared nodes.
-}
encode :: BAC -> String
encode node =
  root node
  |> format 0
  |> (`execState` FormatterState (makePointers 0 node) [] "")
  |> output

-- | print a BAC concisely.  See `encode` for details.
printBAC :: BAC -> IO ()
printBAC = encode .> putStr

{- |
Encode a BAC into a YAML string.

For example:

>>> import BAC.Examples
>>> putStr $ encodeAsYAML cone
- dict: '0->1; 1->2'
  target:
    - dict: '0->1'
      target: &0 []
- dict: '0->3; 1->4; 2->2; 3->6; 4->4'
  target:
    - dict: '0->1; 1->2; 2->3'
      target: &1
        - dict: '0->1'
          target: *0
        - dict: '0->2'
          target: []
    - dict: '0->4; 1->2; 2->3'
      target: *1
-}
encodeAsYAML :: BAC -> String
encodeAsYAML node =
  root node
  |> formatYAML 0
  |> (`execState` FormatterState (makePointers 0 node) [] "")
  |> output

data FormatterState = FormatterState
  {
    pointers :: Map Symbol Int,
    is_init :: [Symbol],
    output :: String
  }

write :: String -> State FormatterState ()
write str = modify \state -> state {output = output state ++ str}

format :: Int -> Arrow -> State FormatterState ()
format level curr = do
  let indent = replicate (level * 2) ' '

  let sym = symbol curr
  state <- get
  let ptr = lookup sym (pointers state)

  case ptr of
    Just n | sym `elem` is_init state -> do
      write $ indent ++ "*" ++ show n ++ "\n"
    _ -> do
      case ptr of
        Just n -> do
          modify \st -> st { is_init = sym : is_init state }
          write $ indent ++ "&" ++ show n ++ "\n"
        Nothing -> do
          write ""
      edges (target curr) |> traverse_ \edge -> do
        write $ indent ++ "- " ++ encodeDict (dict edge) ++ "\n"
        format (level + 1) (curr `join` edge)

formatYAML :: Int -> Arrow -> State FormatterState ()
formatYAML level curr =
  edges (target curr) |> traverse_ \edge -> do
    let indent = replicate (level * 4) ' '

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
        modify \st -> st { is_init = sym : is_init state }
        write $ "  target: &" ++ show n
      Nothing -> do
        write "  target:"

    case ptr of
      Just _ | sym `elem` is_init state -> write "\n"
      _ | null (edges (target arr)) -> write " []\n"
      _ -> do
        write "\n"
        formatYAML (level + 1) arr
