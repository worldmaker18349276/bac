{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Utils.LabelBigraph where

import Data.List.Extra (groupSortOn)
import Data.List (sort, findIndex, delete)
import Data.Maybe (fromJust)
import Data.Either (partitionEithers)
import Data.Bifunctor (bimap)

-- BUG: this method is wrong.  refinement may change the order of key.

refine :: (Eq a, Eq b) => [(a, b)] -> ([[a]], [[b]]) -> ([[a]], [[b]])
refine bigraph (left, right) =
  (concatMap (groupSortOn leftKey) left, concatMap (groupSortOn rightKey) right)
  where
  leftKey a = sort $ (\(_, b) -> fromJust $ findIndex (elem b) right) <$> filter ((== a) . fst) bigraph
  rightKey b = sort $ (\(a, _) -> fromJust $ findIndex (elem a) left) <$> filter ((== b) . snd) bigraph

refineFix :: (Eq a, Eq b) => [(a, b)] -> ([[a]], [[b]]) -> ([[a]], [[b]])
refineFix bigraph leftright =
  let leftright' = refine bigraph leftright
  in if leftright' == leftright then leftright' else refineFix bigraph leftright'

singleOut :: Eq a => Int -> a -> [[a]] -> [[a]]
singleOut _ _ [] = []
singleOut 0 _a ([a]:t) = [a] : t
singleOut 0 a (h:t) = if a `elem` h then [a] : delete a h : t else h : t
singleOut i a (h:t) = h : singleOut (i-1) a t

data LoopState b = Start Int | Middle Int Int [b]

next :: (Eq a, Eq b) => [(a, b)] -> (LoopState b, ([[a]], [[b]])) -> [(Maybe (LoopState b, (Int, Int)), ([[a]], [[b]]))]
next bigraph (input_state, (left, right)) =
  case input_state of
    Start i | i > length left -> [(Nothing, (left, right))]
    Start i -> do
      a <- left !! i
      let (left', right') = refineFix bigraph (singleOut i a left, right)
      let bs = snd <$> filter ((== a) . fst) bigraph
      next bigraph (Middle i 0 bs, (left', right'))
    Middle i j _ | j > length right -> next bigraph (Start (i+1), (left, right))
    Middle i j bs | head (right !! j) `notElem` bs -> next bigraph (Middle i (j+1) bs, (left, right))
    Middle i j bs -> do
      b <- right !! j
      let (left', right') = refineFix bigraph (left, singleOut j b right)
      let key = (i, sum $ length <$> take j right)
      return (Just (Middle i j bs, key), (left', right'))


canonicalizeLabelBigraph :: (Eq a, Eq b) => [(a, b)] -> ([[a]], [[b]]) -> [([a], [b])]
canonicalizeLabelBigraph bigraph (left, right) =
  go [(Start 0, refineFix bigraph (left, right))]
  where
  go state_leftrights =
    case partitionEithers (transform <$> concatMap (next bigraph) state_leftrights) of
      (res, []) -> fmap (concat `bimap` concat) res
      ([], state_leftrights) -> go $ fmap snd $ head $ groupSortOn fst state_leftrights
      _partial_done -> error "invalid state"

  transform :: (Maybe (a, b), c) -> Either c (b, (a, c))
  transform (Just (state, key), leftright) = Right (key, (state, leftright))
  transform (Nothing, leftright) = Left leftright
