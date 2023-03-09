module Main (main) where

import BAC
import Braider
import YAML

import Test.HUnit ((@?=), Test (TestList, TestLabel, TestCase), runTestTT, Counts)
import Data.Maybe (fromMaybe)

test_cone :: Test
test_cone = TestCase $ do
  let cone = braid $ do
        y <- knot' []
        b <- knot' []
        p <- knot' [y]
        c <- knot' [y, b]
        v <- knot' [c, c] // [[0,0], [1,0]] // [[0,1], [1,1]]
        knot' [p, v] // [[1,0], [1,1]] // [[0,0], [1,0,0]]

  putStrLn "#[cone]"
  putStrLn $ cone |> fmap encodeNode' |> fromMaybe "Nothing"
  fmap validate cone @?= Just True

test_torus :: Test
test_torus = TestCase $ do
  let torus = braid $ do
        t <- knot' []
        c <- knot' [t, t]
        c' <- knot' [t, t]
        p <- knot' [c, c', c, c']
          // [[0,1], [1,0]]
          // [[1,1], [2,1]]
          // [[2,0], [3,1]]
          // [[3,0], [0,0]]
        knot' [p]
          // [[0,0], [0,2]]
          // [[0,1], [0,3]]
          -- // [[0,0,0], [0,1,0], [0,2,0], [0,3,0], [0,0,1], [0,1,1], [0,2,1], [0,3,1]]

  putStrLn "#[torus]"
  putStrLn $ torus |> fmap encodeNode' |> fromMaybe "Nothing"
  fmap validate torus @?= Just True

tests :: Test
tests = TestList [
  TestLabel "test cone" test_cone,
  TestLabel "test torus" test_torus
  ]

main :: IO Counts
main = runTestTT tests
