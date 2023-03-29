module BAC.Examples where

import BAC.Base
import BAC.Braider
import Data.Maybe (fromJust)
import Data.Map (Map, fromList)

-- $setup
-- The examples run with the following settings:
--
-- >>> import BAC.Serialize

{- |
![cone](./pictures/cone-serialize.png)

>>> printNode' cone
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
-}
cone :: Node ()
cone = fromJust $ braid $ do
  y <- knot' []
  b <- knot' []
  p <- knot' [y]
  c <- knot' [y, b]
  v <- knot' [c, c] // [[0,0], [1,0]] // [[0,1], [1,1]]
  knot' [p, v] // [[1,0], [1,1]] // [[0,0], [1,0,0]]

coneNames :: Map Symbol String
coneNames = fromList
  [
    (0, "void"),
    (1, "tip"),
    (2, "side"),
    (3, "point"),
    (4, "circle"),
    (6, "bottom")
  ]

{- |
![torus](./pictures/torus-serialize.png)

>>> printNode' torus
- 0->1; 1->2; 2->3; 3->3; 4->5; 6->3; 7->2; 8->3; 10->5
  - 0->1; 1->2; 2->3
    &0
    - 0->1
      &1
    - 0->2
      *1
  - 0->4; 1->3; 2->6
    &2
    - 0->1
      *1
    - 0->2
      *1
  - 0->7; 1->8; 2->6
    *0
  - 0->10; 1->2; 2->8
    *2
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

torusNames :: Map Symbol String
torusNames = fromList
  [
    (0, "void"),
    (1, "point"),
    (2, "circle"),
    (3, "torus"),
    (5, "circle'")
  ]

{- |

![crescent](./pictures/crescent-serialize.png)

>>> printNode' crescent
- 0->1; 1->2; 2->3; 3->4; 5->2; 6->3; 7->4
  - 0->1; 1->2
    &0
    - 0->1
      &1
  - 0->3; 1->2
    &2
    - 0->1
      *1
  - 0->5; 1->6
    *0
  - 0->7; 1->6
    *2
-}
crescent :: Node ()
crescent = fromJust $ braid $ do
  s <- knot' []
  c <- knot' [s]
  c' <- knot' [s]
  p <- knot' [c, c', c, c']
    // [[0,0], [1,0]]
    // [[2,0], [3,0]]
  knot' [p]
    // [[0,0,0], [0,1,0]]
    // [[0,0], [0,2]]
    // [[0,1], [0,3]]

crescentNames :: Map Symbol String
crescentNames = fromList
  [
    (0, "void"),
    (1, "point"),
    (2, "circle"),
    (3, "crescent"),
    (4, "circle'")
  ]
