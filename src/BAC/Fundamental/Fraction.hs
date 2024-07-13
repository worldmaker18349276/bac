{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BAC.Fundamental.Fraction (
  Cofraction,
  Fraction,
  validateCofraction,
  validateFraction,
  extendCofraction,
  extendFraction,
  compatibleFractions,
  compatibleCofractions,
  compatibleCofractionsFractions,
  findValidCofractionsFractions,
) where

import Control.Monad (guard, mzero)
import Data.Bifunctor (second)
import Data.Foldable (find)
import Data.List (sort)
import Data.List.Extra (allSame, anySame, groupSortOn, nubSort, nubSortOn)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust, isJust)
import Data.Tuple.Extra (both)

import BAC.Base
import Utils.Utils (guarded, (.>), (|>))

-- $setup
-- >>> import BAC.Serialize
-- >>> import BAC.Fundamental
-- >>> import BAC.Examples (cone, torus, crescent)


-- | Two pairs of symbols representing two morphisms with the same starting node.  The
--   first pair of symbols is called numerator; the second pair of symbols is called
--   denominator.
type Cofraction = ((Symbol, Symbol), (Symbol, Symbol))

-- | Two pairs of symbols representing two morphisms with the same ending node. The first
--   pair of symbols is called numerator; the second pair of symbols is called
--   denominator.
type Fraction = ((Symbol, Symbol), (Symbol, Symbol))


-- | Check whether a given value is a valid cofraction.  A valid cofraction obey: coforks
--   of the denominator are also coforks of the numerator.  A cofork of a morphism `f` is
--   a pair of distinct morphisms @(g, g')@ such that @f . g = f . g'@.
validateCofraction :: Monoid e => BAC e -> Cofraction -> Bool
validateCofraction node (n, d) = isJust do
  -- ensure that `n`, `d` are reachable
  n_arr_arr <- arrow2 node n
  d_arr_arr <- arrow2 node d
  -- ensure that `n_arr_arr` and `d_arr_arr` start at the same node
  guard $ symbol (fst n_arr_arr) == symbol (fst d_arr_arr)
  let sym0 = symbol (fst n_arr_arr)

  -- ensure that all coforks of `n` are also coforks of `d`
  guard $
    -- find all nondecomposable incoming edges
    suffixND node sym0
    -- group them to form coforks of `d_arr_arr`
    |> groupSortOn (second (`join` snd d_arr_arr) .> symbol2)
    -- for each group, they should also be cofork of `n_arr_arr`
    |> all (fmap (second (`join` snd n_arr_arr) .> symbol2) .> allSame)

-- | Check whether a given value is a valid fraction.  A valid fraction obey: forks of the
--   denominator are also forks of the numerator.  A fork of a morphism `f` is a pair of
--   distinct morphisms @(g, g')@ such that @g . f = g' . f@.
validateFraction :: Monoid e => BAC e -> Fraction -> Bool
validateFraction node (n, d) = isJust do
  -- ensure that `n`, `d` are reachable
  n_arr_arr <- arrow2 node n
  d_arr_arr <- arrow2 node d
  -- ensure that `n_arr_arr` and `d_arr_arr` end at the same node
  guard $ symbol (uncurry join n_arr_arr) == symbol (uncurry join d_arr_arr)
  let node0 = target (uncurry join n_arr_arr)

  -- ensure that all forks of `n` are also forks of `d`
  guard $
    -- find all nondecomposable outgoing edges
    edgesND node0
    -- group them to form forks of `d`
    |> groupSortOn ((snd d_arr_arr `join`) .> symbol)
    -- for each group, they should also be fork of `n`
    |> all (fmap ((snd n_arr_arr `join`) .> symbol) .> allSame)


-- | Extend a cofraction with an arrow ending at the vertex of this cofraction.
--   An extended valid cofraction is also a valid cofraction.
extendCofraction :: Monoid e => BAC e -> (Symbol, Symbol) -> Cofraction -> Maybe Cofraction
extendCofraction node q (n, d) = do
  -- ensure `q`, `n`, `d` are reachable
  (q_arr, q_subarr) <- arrow2 node q
  (n_arr, n_subarr) <- arrow2 node n
  (d_arr, d_subarr) <- arrow2 node d
  -- ensure `q` and `n`/`d` are composable
  guard $
    symbol n_arr == symbol d_arr
    && symbol n_arr == symbol (q_arr `join` q_subarr)
  -- compose arrow and edges
  let n' = symbol2 (q_arr, q_subarr `join` n_subarr)
  let d' = symbol2 (q_arr, q_subarr `join` d_subarr)
  return (n', d')

-- | Extend a fraction with an arrow starting at the vertex of this fraction.
--   An extended valid fraction is also a valid fraction.
extendFraction :: Monoid e => BAC e -> Fraction -> (Symbol, Symbol) -> Maybe Fraction
extendFraction node (n, d) q = do
  -- ensure `q`, `n`, `d` are reachable
  (q_arr, q_subarr) <- arrow2 node q
  (d_arr, d_subarr) <- arrow2 node d
  (n_arr, n_subarr) <- arrow2 node n
  -- ensure `n`/`d` and `q` are composable
  guard $
    symbol (n_arr `join` n_subarr) == symbol (d_arr `join` d_subarr)
    && symbol q_arr == symbol (d_arr `join` d_subarr)
  -- compose edges and arrow
  let n' = symbol2 (n_arr, n_subarr `join` q_subarr)
  let d' = symbol2 (d_arr, d_subarr `join` q_subarr)
  return (n', d')


-- | Check whether a list of fractions are compatible with each other.
--   Fraction @(n, d)@ and fraction @(n', d')@ are compatible if @q . d = q' . d'@ implies
--   @q . n = q' . n'@ for all `q` and 'q''.  That is, two fractions are compatible if
--   their extensions are unique on the denominator.
--   A valid fraction is compatible with itself.
compatibleFractions :: Monoid e => BAC e -> [Fraction] -> Bool
compatibleFractions node fractions = isJust do
  -- ensure that all denominators/numerators of fractions start at the same node
  guard $ fractions |> fmap (both fst) |> allSame

  pairs <- fractions |> traverse \(n, d) -> do
    n_arr_arr <- arrow2 node n
    d_arr_arr <- arrow2 node d
    -- zip values of dictionaries of the denominator and the numerator
    -- which form pairs between symbols on the starting nodes of those two edges
    let n_syms = n_arr_arr |> snd |> dict |> Map.elems
    let d_syms = d_arr_arr |> snd |> dict |> Map.elems
    return $ n_syms `zip` d_syms
  
  -- if two pairs have the same second symbol, their first symbols should also be the same
  guard $ pairs |> concat |> nubSort |> fmap snd |> anySame |> not

-- | Check whether a list of cofractions are compatible.
--   Cofraction @(n, d)@ and cofraction @(n', d')@ are compatible if @d . q = d' . q'@
--   implies @n . q = n' . q'@ for all `q` and 'q''.  That is, two cofractions are
--   compatible if their extensions are unique on the denominator.
--   A valid cofraction is compatible with itself.
--   For simplicity, we assume that the denominators of cofractions are edges of the node.
--   In fact, we only deal with fractions and cofractions whose denominators are
--   nondecomposable.
compatibleCofractions :: Monoid e => BAC e -> [Cofraction] -> Bool
compatibleCofractions _ [] = True
compatibleCofractions node cofractions = isJust do
  -- ensure that all denominators/numerators of cofractions end at the same node
  (_, sym0) <-
    cofractions
    |> fmap (both (arrow2 node .> fromJust .> uncurry join .> symbol))
    |> guarded allSame
    |> fmap head
  
  sequence_ $ root node |> foldUnder sym0 \curr results -> do
    results' <- traverse sequence results

    -- find extended cofraction whose vertex is this node, and return two symbols referencing
    -- the denominator and the numerator of this cofraction.
    let pairs = do
          (res, edge) <- results' `zip` edges (target curr)
          case res of
            AtOuter -> mzero
            AtInner subpairs -> subpairs |> fmap (both (dict edge !))
            AtBoundary ->
              cofractions
              |> find (snd .> (== symbol2 (curr, edge)))
              |> fmap (both snd)
              |> maybe mzero return

    -- if two pairs have the same second symbol, their first symbols should also be the same
    pairs |> nubSort |> guarded (fmap snd .> anySame .> not)

-- | Check whether cofractions and fractions are compatible each others.
--   Cofraction @(n, d)@ and fraction @(n', d')@ are compatible if @n' . d = d' . n@.
compatibleCofractionsFractions :: Monoid e => BAC e -> [Cofraction] -> [Fraction] -> Bool
compatibleCofractionsFractions node cofractions fractions =
  isJust $
    cofractions |> traverse \(n, d) -> do
      fractions |> traverse \(n', d') -> do
        n_arr_arr <- arrow2 node n
        d_arr_arr <- arrow2 node d
        n_arr_arr' <- arrow2 node n'
        d_arr_arr' <- arrow2 node d'

        -- ensure ending node of the denominator of cofraction is the starting node of the
        -- numerator of fraction
        guard $ symbol (uncurry join d_arr_arr) == symbol (fst n_arr_arr')
        -- ensure ending node of the numerator of cofraction is the starting node of the
        -- denominator of fraction
        guard $ symbol (uncurry join n_arr_arr) == symbol (fst d_arr_arr')

        -- compose the denominator of cofraction and the numerator of fraction
        -- and compose the numerator of cofraction and the denominator of fraction
        -- they should be the same
        let arr = snd d_arr_arr `join` snd n_arr_arr'
        let arr' = snd n_arr_arr `join` snd d_arr_arr'
        guard $ symbol arr == symbol arr'

{- |
Find all valid nondecomposable cofractions and fractions, which is used for adding a
morphism.  The results are the fractions and cofractions need to be selected, or Nothing
if it is invalid.  There may have zero option to select, which indicates it is impossible
to add a morphism.

Examples:

>>> fromJust $ findValidCofractionsFractions 1 6 cone
([[((0,6),(0,1))]],[])
-}
findValidCofractionsFractions ::
  Monoid e
  => Symbol
  -- ^ The symbol indicating the source object of the morphism to be added.
  -> Symbol
  -- ^ The symbol indicating the target object of the morphism to be added.
  -> BAC e
  -- ^ The root node of BAC.
  -> Maybe ([[Cofraction]], [[Fraction]])
  -- ^ The cofractions and fractions need to be selected, or Nothing if it is invalid to
  --   add such morphism.
findValidCofractionsFractions src tgt node = do
  -- ensure that `src` and `tgt` are reachable, and check the order between `src` and `tgt`
  src_arr <- arrow node src
  tgt_arr <- arrow node tgt
  guard $ locate tgt_arr src == Outer

  let src_alts =
        suffixND node src
        |> nubSortOn symbol2
        |> fmap \(arr, edge) -> sort do
          -- construct nondecomposable cofraction and validate it
          arr' <- arr `divide` tgt_arr
          let cofraction = (symbol2 (arr, arr'), symbol2 (arr, edge))
          guard $ validateCofraction node cofraction
          return cofraction
  let tgt_alts =
        edgesND (target tgt_arr)
        |> nubSortOn symbol
        |> fmap \edge -> sort do
          -- construct nondecomposable fraction and validate it
          arr' <- src_arr `divide` (tgt_arr `join` edge)
          let fraction = (symbol2 (src_arr, arr'), symbol2 (tgt_arr, edge))
          guard $ validateFraction node fraction
          return fraction
  return (src_alts, tgt_alts)
