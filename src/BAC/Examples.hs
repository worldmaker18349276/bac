module BAC.Examples (cone, torus, crescent) where

import BAC.Base
import BAC.Braider
import Data.Maybe (fromJust)

-- $setup
-- The examples run with the following settings:
--
-- >>> import BAC.Serialize

{- |
![cone](./img/cone-serialize.png)

>>> printBAC cone
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
cone :: BAC
cone = fromJust $ braid $ do
  y <- knot []
  b <- knot []
  p <- knot [y]
  c <- knot [y, b]
  v <- knot [c, c]
    // [Path [0,0], Path [1,0]]
    // [Path [0,1], Path [1,1]]
  knot [p, v]
    // [Path [1,0], Path [1,1]]
    // [Path [0,0], Path [1,0,0]]

{- |
![torus](./img/torus-serialize.png)

>>> printBAC torus
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
torus :: BAC
torus = fromJust $ braid $ do
  t <- knot []
  c <- knot [t, t]
  c' <- knot [t, t]
  p <- knot [c, c', c, c']
    // [Path [0,1], Path [1,0]]
    // [Path [1,1], Path [2,1]]
    // [Path [2,0], Path [3,1]]
    // [Path [3,0], Path [0,0]]
  knot [p]
    // [Path [0,0], Path [0,2]]
    // [Path [0,1], Path [0,3]]

{- |

![crescent](./img/crescent-serialize.png)

>>> printBAC crescent
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
crescent :: BAC
crescent = fromJust $ braid $ do
  s <- knot []
  c <- knot [s]
  c' <- knot [s]
  p <- knot [c, c', c, c']
    // [Path [0,0], Path [1,0]]
    // [Path [2,0], Path [3,0]]
  knot [p]
    // [Path [0,0,0], Path [0,1,0]]
    // [Path [0,0], Path [0,2]]
    // [Path [0,1], Path [0,3]]
