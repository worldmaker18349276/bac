module BAC.Examples where

import BAC.Base
import BAC.Braider
import Data.Maybe (fromJust)

-- $setup
-- The examples run with the following settings:
--
-- >>> import BAC.YAML

{- |
>>> putStrLn $ encodeNode' cone
- dict: '0->1; 1->2'
  node:
    - dict: '0->1'
      node: &0 []
- dict: '0->3; 1->4; 2->2; 3->6; 4->4'
  node:
    - dict: '0->1; 1->2; 2->3'
      node: &1
        - dict: '0->1'
          node: *0
        - dict: '0->2'
          node: []
    - dict: '0->4; 1->2; 2->3'
      node: *1
<BLANKLINE>
-}
cone :: Node ()
cone = fromJust $ braid $ do
  y <- knot' []
  b <- knot' []
  p <- knot' [y]
  c <- knot' [y, b]
  v <- knot' [c, c] // [[0,0], [1,0]] // [[0,1], [1,1]]
  knot' [p, v] // [[1,0], [1,1]] // [[0,0], [1,0,0]]

{- |
>>> putStrLn $ encodeNode' torus
- dict: '0->1; 1->2; 2->3; 3->3; 4->5; 6->3; 7->2; 8->3; 10->5'
  node:
    - dict: '0->1; 1->2; 2->3'
      node: &0
        - dict: '0->1'
          node: &1 []
        - dict: '0->2'
          node: *1
    - dict: '0->4; 1->3; 2->6'
      node: &2
        - dict: '0->1'
          node: *1
        - dict: '0->2'
          node: *1
    - dict: '0->7; 1->8; 2->6'
      node: *0
    - dict: '0->10; 1->2; 2->8'
      node: *2
<BLANKLINE>
-}
torus :: Node ()
torus = fromJust $ braid $ do
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

{- |
>>> putStrLn $ encodeNode' crescent
- dict: '0->1; 1->2; 2->3; 3->2; 5->6; 6->3; 7->6'
  node:
    - dict: '0->1; 1->2'
      node: &0
        - dict: '0->1'
          node: &1 []
    - dict: '0->3; 1->2'
      node: *0
    - dict: '0->5; 1->6'
      node: &2
        - dict: '0->1'
          node: *1
    - dict: '0->7; 1->6'
      node: *2
<BLANKLINE>
-}
crescent :: Node ()
crescent = fromJust $ braid $ do
  s <- knot' []
  c <- knot' [s]
  c' <- knot' [s]
  p <- knot' [c, c, c', c']
    // [[0,0], [1,0]]
    // [[2,0], [3,0]]
  knot' [p]
    // [[0,0,0], [0,2,0]]
    // [[0,0], [0,1]]
    // [[0,2], [0,3]]
