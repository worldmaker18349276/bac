{-# LANGUAGE BlockArguments #-}

module BAC.Serialize (serializeDict, serializeAsYAML, serialize, printBAC, serializeWithValue, printBACWithValue) where

import Control.Monad (when)
import Control.Monad.State (MonadState (get), State, execState, modify)
import Data.Foldable (traverse_)
import Data.List (intercalate)
import Data.Map (Map, fromList, lookup, toList)
import Data.Tuple.Extra (both)
import Prelude hiding (lookup)

import BAC.Base hiding (modify)
import Utils.Utils ((.>), (|>))

-- | Serialize dictionary as a string concisely.
serializeDict :: Dict -> String
serializeDict =
  toList
  .> fmap (both show)
  .> fmap (\(k, v) -> k ++ "->" ++ v)
  .> intercalate "; "

-- | Count the number of shown references.
countRef :: Monoid e => Arrow e -> [(Symbol, Int)]
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
makePointers :: (Enum p, Monoid e) => p -> BAC e -> Map Symbol p
makePointers p =
  root
  .> countRef
  .> filter (snd .> (> 1))
  .> fmap fst
  .> (`zip` [p..])
  .> fromList

{- |
Serialize a BAC into a YAML-like string.

For example:

>>> import BAC.Examples
>>> putStr $ serialize cone
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
serialize :: BAC () -> String
serialize node =
  root node
  |> format (\_ _ -> "") 0
  |> (`execState` FormatterState (makePointers 0 node) [] "")
  |> output

{- |
Serialize a BAC into a YAML-like string with edge value.

For example:

>>> import BAC.Examples
>>> putStr $ serializeWithValue cone
- 0->1; 1->2
  ()
  - 0->1
    ()
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4
  ()
  - 0->1; 1->2; 2->3
    ()
    &1
    - 0->1
      ()
      *0
    - 0->2
      ()
  - 0->4; 1->2; 2->3
    ()
    *1
-}
serializeWithValue :: (Monoid e, Show e) => BAC e -> String
serializeWithValue node =
  root node
  |> format (\indent val -> indent ++ show val ++ "\n") 0
  |> (`execState` FormatterState (makePointers 0 node) [] "")
  |> output

-- | print a BAC concisely.  See `serialize` for details.
printBAC :: BAC () -> IO ()
printBAC = serialize .> putStr

printBACWithValue :: (Monoid e, Show e) => BAC e -> IO ()
printBACWithValue = serializeWithValue .> putStr

{- |
Serialize a BAC into a YAML string.

For example:

>>> import BAC.Examples
>>> putStr $ serializeAsYAML cone
- dict: '0->1; 1->2'
  value: ()
  target:
    - dict: '0->1'
      value: ()
      target: &0 []
- dict: '0->3; 1->4; 2->2; 3->6; 4->4'
  value: ()
  target:
    - dict: '0->1; 1->2; 2->3'
      value: ()
      target: &1
        - dict: '0->1'
          value: ()
          target: *0
        - dict: '0->2'
          value: ()
          target: []
    - dict: '0->4; 1->2; 2->3'
      value: ()
      target: *1
-}
serializeAsYAML :: (Monoid e, Show e) => BAC e -> String
serializeAsYAML node =
  root node
  |> formatYAML show 0
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

format :: Monoid e => (String -> e -> String) -> Int -> Arrow e -> State FormatterState ()
format format_value level curr = do
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
        write $ indent ++ "- " ++ serializeDict (dict edge) ++ "\n"
        write $ format_value (indent ++ "  ") (value edge)
        format format_value (level + 1) (curr `join` edge)

formatYAML :: Monoid e => (e -> String) -> Int -> Arrow e -> State FormatterState ()
formatYAML format_value level curr =
  edges (target curr) |> traverse_ \edge -> do
    let indent = replicate (level * 4) ' '

    write $ indent ++ "- dict: '" ++ serializeDict (dict edge) ++ "'\n"
    write $ indent ++ "  value: " ++ format_value (value edge) ++ "\n"
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
        formatYAML format_value (level + 1) arr
