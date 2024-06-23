{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module BAC.Fundamental.Split (
  partitionPrefixesSuffixes,
  partitionPrefixes,
  partitionSuffixes,
  unsplittable,
  partitionSymbols,
  splitSymbol,
  splitSymbolOnRoot,
  splitNode,
  splitRootNode,
) where

import Control.Monad (guard)
import Data.Foldable.Extra (notNull)
import Data.List (sort, sortOn, find)
import Data.List.Extra (anySame, disjoint, nubSortOn, replace)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.DisjointSet (bipartiteEqclass, bipartiteEqclassOn)
import Utils.Utils (zipIf, (.>), (|>))
import Control.Arrow (first)

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)
-- >>> import Data.Maybe (fromJust)

partitionPrefixesSuffixes :: Monoid e => BAC e -> Symbol -> [([(Arrow e, Arrow e)], [(Arrow e, Arrow e)])]
partitionPrefixesSuffixes node tgt =
  prefix node tgt
  |> nubSortOn symbol2
  -- suffix decomposition: `arr23` => `(arr2, arr3)`
  |> concatMap (\(arr1, arr23) -> suffix (target arr1) (symbol arr23) |> nubSortOn symbol2 |> fmap (arr1,))
  -- connect prefix and suffix
  |> fmap (\(arr1, (arr2, arr3)) -> ((arr1, arr2 `join` arr3), (arr1 `join` arr2, arr3)))
  -- classify prefixes and suffixes by connectivity
  |> bipartiteEqclassOn symbol2 symbol2
  |> fmap (both (sortOn symbol2))
  |> sortOn (both (fmap symbol2))

{- |
Partition the prefixes of an arrow.  It returns a partition of @prefix node tgt@ excluding
@(tgt, base)@.  The objects represented by the elements in each group are unsplittable in
the section category of the arrow specified by `tgt`.

Examples:

>>> partitionPrefixes cone 2
[[(1,1)],[(3,2)]]

>>> partitionPrefixes (target $ fromJust $ arrow cone 3) 2
[[(1,1)],[(4,1)]]
-}
partitionPrefixes :: Monoid e => BAC e -> Symbol -> [[(Symbol, Symbol)]]
partitionPrefixes node tgt = partitionPrefixesSuffixes node tgt |> fmap (fst .> fmap symbol2)

partitionSuffixes :: Monoid e => BAC e -> Symbol -> [[(Symbol, Symbol)]]
partitionSuffixes node tgt = partitionPrefixesSuffixes node tgt |> fmap (snd .> fmap symbol2)

prefix2 :: Monoid e => BAC e -> (Arrow e, Arrow e) -> (Arrow e, Arrow e)
prefix2 node =
    first (symbol .> prefix node .> head)
    .> \((arr1, arr2), arr3) -> (arr1, arr2 `join` arr3)

unsplittable :: Monoid e => BAC e -> (Arrow e, Arrow e) -> (Arrow e, Arrow e) -> Bool
unsplittable node arr_arr1 arr_arr2 =
  (symbol2 arr_arr1 |> \(s1, s2) -> s1 /= base && s2 /= base)
  && (symbol2 arr_arr2 |> \(s1, s2) -> s1 /= base && s2 /= base)
  && sym1 == sym2 && sameGroup
  where
  sym1 = symbol (uncurry join arr_arr1)
  sym2 = symbol (uncurry join arr_arr2)
  sym_sym1 = prefix2 node arr_arr1 |> symbol2
  sym_sym2 = prefix2 node arr_arr2 |> symbol2
  sameGroup =
    partitionPrefixes node sym1
    |> find (elem sym_sym1)
    |> fromJust
    |> elem sym_sym2

isPartition :: Eq a => [[a]] -> Bool
isPartition partition = concat partition |> anySame |> not

-- | Ckeck if `partition1` is finer than `partition2`: if two elements are in the same
--   part in `partition1`, they are also in the same part in `partition2`.
finer :: Ord a => [[a]] -> [[a]] -> Bool
finer partition1 partition2 = isPartition partition1 && sameHost && include
  where
  sameHost = sort (concat partition1) == sort (concat partition2)
  include =
    partition1
    |> all \group ->
      partition2
      |> all \group' ->
        group `disjoint` group' || group `subset` group'
  subset a b = a |> all (`elem` b)

{- |
Split a symbol on a node, with two parameters @(src, tgt) :: (Symbol, Symbol)@ and
@partition :: [(Symbol, [(Symbol, Symbol)])]@ and @direct_splitted_symbols :: [Symbol]@.
`src` indicates the node to operate, `tgt` indicates the symbol to split, and `partition`
is a list of splitted symbols and the corresponding group of splitted prefixes, which
should be an union of some groups given by `partitionPrefixes`.  `direct_splitted_symbols`
is the splitted symbols for each direct edge of @(src, tgt)@.  If there is a
splitted symbol which has an empty group, it should be an direct edge being classified to
this symbol.

In categorical perspectives, it splits a non-terminal morphism, where @(src, tgt)@
indicates a proper morphism to split, and @(src, sym)@ for all @(sym, grps) <- partition@
will indicate a splitted morphism, and the morphism chains in the group `grps` will
compose to this morphism.  A splitted morphism which no morphism chains compose to is
nondecomposable.

Examples:

>>> let partition_cone02 = [(2,[(1,1)]),(7,[(3,2)])]
>>> printBAC $ fromJust $ splitSymbol (0,2) partition_cone02 [] cone
- 0->1; 1->2
  - 0->1
- 0->3; 1->4; 2->7; 3->6; 4->4
  - 0->1; 1->2; 2->3
    &0
    - 0->1
    - 0->2
  - 0->4; 1->2; 2->3
    *0

>>> let partition_cone32 = [(5,[(1,1)]),(6,[(4,1)]),(7,[])]
>>> let cone' = fromJust $ addEdge (3,2) () cone
>>> printBAC $ fromJust $ splitSymbol (3,2) partition_cone32 [7] cone'
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 3->6; 4->4; 5->2; 6->2; 7->2
  - 0->7
    *0
  - 0->1; 1->5; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->4; 1->6; 2->3
    *1
-}
splitSymbol ::
  Monoid e
  => (Symbol, Symbol)
  -- ^ The pair of symbols referencing the arrow to split.
  -> [(Symbol, [(Symbol, Symbol)])]
  -- ^ List of splitted symbol and corresponding splitted group of prefixes.
  -> [Symbol]
  -- ^ The list of splitted symbols for each the direct edge.
  -> BAC e
  -> Maybe (BAC e)
splitSymbol (src, tgt) partition direct_splitted_symbols node = do
  -- ensure that `(src, tgt)` is reachable and proper
  (src_arr, _tgt_subarr) <- arrow2 node (src, tgt)
  guard $ tgt /= base
  let src_node = target src_arr

  -- ensure that every splittable groups have been classified to splitted symbols
  let splittable_groups = partitionPrefixes src_node tgt
  guard $ isPartition (fmap snd partition)
  guard $ splittable_groups `finer` fmap snd partition

  -- ensure each direct edge will be classified to a splitted symbol
  let direct_edge_count =
        edges src_node
        |> filter (symbol .> (== tgt))
        |> length
  guard $ length direct_splitted_symbols == direct_edge_count
  guard $ direct_splitted_symbols |> all (`elem` fmap fst partition)

  -- ensure each splitted symbol should have been classified by at least one edge
  guard $ partition |> all \(s, splitted_group) ->
    notNull splitted_group || (s `elem` direct_splitted_symbols)

  -- validate splitted symbols
  guard $ src_node |> symbols |> replace [tgt] (fmap fst partition) |> anySame |> not

  -- classify each prefix to a splitted symbol
  let partition_mapping =
        partition
        |> concatMap sequence
        |> fmap swap
        |> Map.fromList

  let src_node' = BAC do
        (sym, edge) <- zipIf (symbol .> (== tgt)) direct_splitted_symbols (edges src_node)
        let splitted_dict =
              dict edge
              |> Map.mapWithKey \s r ->
                if r /= tgt then r
                else if s /= base then partition_mapping ! (symbol edge, s)
                else fromJust sym
        return edge {dict = splitted_dict}

  fromReachable src_node' $ root node |> modifyUnder src \(_curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {target = subnode}
    AtBoundary -> return edge {dict = merged_dict, target = src_node'}
      where
      -- map splitted symbols like before splitting
      merge (s, r) = if s == tgt then fmap fst partition |> fmap (, r) else [(s, r)]
      merged_dict = dict edge |> Map.toList |> concatMap merge |> Map.fromList

-- | Split a symbol on the root node (split an initial morphism).  See `splitSymbol` for
--   details.
splitSymbolOnRoot :: Monoid e => Symbol -> [(Symbol, [(Symbol, Symbol)])] -> [Symbol] -> BAC e -> Maybe (BAC e)
splitSymbolOnRoot tgt = splitSymbol (base, tgt)

{- |
Partition symbols on a node.
It returns a partition of `symbols` of the given node excluding `base`, where the objects
represented by the elements in each group are unsplittable in the given bounded acyclic
category.

Examples:

>>> partitionSymbols $ cone
[[1,2,3,4,6]]

>>> partitionSymbols $ target $ fromJust $ arrow cone 4
[[1],[2]]

>>> partitionSymbols $ target $ fromJust $ arrow crescent 1
[[1,2,3],[5,6,7]]
-}
partitionSymbols :: BAC e -> [[Symbol]]
partitionSymbols =
  edges
  .> fmap (dict .> Map.elems)
  .> zip [0 :: Int ..]
  .> concatMap sequence
  .> bipartiteEqclass
  .> fmap (snd .> sort)
  .> sort

{- |
Split a node, with parameters @tgt :: Symbol@, the symbol of the node to split, and
@partition :: [((Symbol, Symbol) -> Symbol, [Symbol])]@, list of split functions and
splitted groups of symbols coarser than `partitionSymbols`.

In categorical perspectives, it splits a terminal morphism, where `tgt` indicates the
source object of morphism to split.  For all incoming morphisms of this object, say
@(s1, s2)@, the pair of symbol @(s1, splitter (s1, s2))@ for @(splitter, _) <- partition@
will indicate the incoming morphism of splitted object with the same source object.

Examples:

>>> partition = [(makeShifter crescent 0, [1,2,3]), (makeShifter crescent 1, [5,6,7])]
>>> printBAC $ fromJust $ splitNode 1 partition crescent
- 0->1; 1->2; 2->3; 3->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
- 0->5; 5->2; 6->3; 7->4
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2

>>> partition' = [(makeShifter cone 0, [1,2]), (makeShifter cone 1, [])]
>>> printBAC $ fromJust $ splitNode 4 partition' cone
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->4; 2->2; 3->6; 4->4; 5->10; 8->10
  - 0->1; 1->2; 2->3
    &1
    - 0->1
      *0
    - 0->2
  - 0->5
    &2
  - 0->4; 1->2; 2->3
    *1
  - 0->8
    *2
-}
splitNode ::
  Monoid e
  => Symbol
  -- ^ The symbol referencing the node to be splitted.
  -> [((Symbol, Symbol) -> Symbol, [Symbol])]
  -- ^ The splitters and splitted groups of symbols coarser than `partitionSymbols`.
  -> BAC e
  -> Maybe (BAC e)
splitNode tgt partition node = do
  -- ensure that `tgt` is reachable and proper
  tgt_node <- arrow node tgt |> fmap target
  guard $ tgt /= base

  let splitter = partition |> fmap fst |> sequence
  -- validate `splitter`
  guard $
    arrowsUnder node tgt
    |> all \arr ->
      arr
      |> dict
      |> Map.toList
      |> concatMap (\(s1, s2) -> if s2 == tgt then splitter (symbol arr, s1) else [s1])
      |> anySame
      |> not

  -- split `tgt_node`
  tgt_nodes' <- tgt_node |> splitRootNode (fmap snd partition)

  fromInner $ root node |> modifyUnder tgt \(curr, edge) -> \case
    AtOuter -> return edge
    AtInner subnode -> return edge {dict = duplicated_dict, target = subnode}
      where
      -- duplicate links of the base wire of the node of `tgt`
      duplicate (s, r)
        | dict curr ! r == tgt = splitter (symbol (curr `join` edge), s)
                                 `zip` splitter (symbol curr, r)
        | otherwise            = [(s, r)]
      duplicated_dict =
        dict edge |> Map.toList |> concatMap duplicate |> Map.fromList
    AtBoundary -> do
      -- split incoming edges of the node of `tgt`
      let splitted_syms = splitter (symbol curr, symbol edge)
      (tgt_node', sym) <- tgt_nodes' `zip` splitted_syms
      let splitted_dict =
            dict edge
            |> Map.filterWithKey (\s _ -> s `elem` symbols tgt_node')
            |> Map.insert base sym
      return edge {dict = splitted_dict, target = tgt_node'}

{- |
Split a root node (split a BAC), with a parameter @partition :: [[Int]]@, which are
indices to splittable groups representing each splitted category.

Examples:

>>> import Data.Foldable (traverse_)
>>> crescent_1 = target $ fromJust $ arrow crescent 1
>>> traverse_ printBAC $ fromJust $ splitRootNode [[1,2,3],[5,6,7]] crescent_1
- 0->1; 1->2
  - 0->1
    &0
- 0->3; 1->2
  - 0->1
    *0
- 0->5; 1->6
  - 0->1
    &0
- 0->7; 1->6
  - 0->1
    *0
-}
splitRootNode ::
  [[Symbol]]
  -- ^ The splitted groups of symbols finer than `partitionSymbols`.
  -> BAC e
  -> Maybe [BAC e]
splitRootNode partition node = do
  -- ensure that every splittable groups have been classified to splitted symbols
  let splittable_groups = partitionSymbols node
  guard $ splittable_groups `finer` partition

  return do
    group <- partition
    let splitted_edges = node |> edges |> filter (symbol .> (`elem` group))
    return $ BAC splitted_edges
