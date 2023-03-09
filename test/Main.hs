module Main (main) where

import BAC
import Braider

import Test.HUnit ((@?=), Test (TestList, TestLabel, TestCase), runTestTT, Counts)

cone :: Maybe (Node Int String)
cone = braid $ do
  y <- knot "side" []
  b <- knot "bottom" []
  p <- knot "tip" [(2, y)]
  c <- knot "circle" [(1, y), (-1, b)]
  v <- knot "point" [(1, c), (-1, c)]
    // [[0,0], [1,0]]
    // [[0,1], [1,1]]
  knot "void" [(1, p), (1, v)]
    // [[1,0], [1,1]]
    // [[0,0], [1,0,0]]

test_cone :: Test
test_cone = TestCase $ do
  print cone
  fmap validate cone @?= Just True

torus :: Maybe (Node Int String)
torus = braid $ do
  t <- knot "torus" []
  c <- knot "circle" [(1, t), (-1, t)]
  c' <- knot "circle'" [(1, t), (-1, t)]
  p <- knot "intersected point" [(1, c), (1, c'), (-1, c), (-1, c')]
    // [[0,1], [1,0]]
    // [[1,1], [2,1]]
    // [[2,0], [3,1]]
    // [[3,0], [0,0]]
  knot "void" [(1, p)]
    // [[0,0], [0,2]]
    // [[0,1], [0,3]]
    -- // [[0,0,0], [0,1,0], [0,2,0], [0,3,0], [0,0,1], [0,1,1], [0,2,1], [0,3,1]]

test_torus :: Test
test_torus = TestCase $ do
  print torus
  fmap validate torus @?= Just True

tests :: Test
tests = TestList [
  TestLabel "test cone" test_cone,
  TestLabel "test torus" test_torus
  ]

main :: IO Counts
main = runTestTT tests
