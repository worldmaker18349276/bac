module BAC.Examples (cone, torus, crescent, cone', torus', crescent') where

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
cone :: BAC ()
cone = fromJust $ braid $ do
  y <- knot []
  b <- knot []
  p <- knot [Edge () y]
  c <- knot [Edge () y, Edge () b]
  v <- knot [Edge () c, Edge () c]
    // [Path [0,0], Path [1,0]]
    // [Path [0,1], Path [1,1]]
  knot [Edge () p, Edge () v]
    // [Path [1,0], Path [1,1]]
    // [Path [0,0], Path [1,0,0]]

cone' :: BAC String
cone' = fromJust $ braid $ do
  y <- knot []
  b <- knot []
  p <- knot [Edge "py" y]
  c <- knot [Edge "cy" y, Edge "cb" b]
  v <- knot [Edge "vc1" c, Edge "vc2" c]
    // [Path [0,0], Path [1,0]]
    // [Path [0,1], Path [1,1]]
  knot [Edge "0p" p, Edge "0v" v]
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
torus :: BAC ()
torus = fromJust $ braid $ do
  t <- knot []
  c <- knot [Edge () t, Edge () t]
  c' <- knot [Edge () t, Edge () t]
  p <- knot [Edge () c, Edge () c', Edge () c, Edge () c']
    // [Path [0,1], Path [1,0]]
    // [Path [1,1], Path [2,1]]
    // [Path [2,0], Path [3,1]]
    // [Path [3,0], Path [0,0]]
  knot [Edge () p]
    // [Path [0,0], Path [0,2]]
    // [Path [0,1], Path [0,3]]

torus' :: BAC String
torus' = fromJust $ braid $ do
  t <- knot []
  c <- knot [Edge "ct1" t, Edge "ct2" t]
  c' <- knot [Edge "c't1" t, Edge "c't2" t]
  p <- knot [Edge "pc1" c, Edge "pc'1" c', Edge "pc2" c, Edge "pc'2" c']
    // [Path [0,1], Path [1,0]]
    // [Path [1,1], Path [2,1]]
    // [Path [2,0], Path [3,1]]
    // [Path [3,0], Path [0,0]]
  knot [Edge "0p" p]
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
crescent :: BAC ()
crescent = fromJust $ braid $ do
  s <- knot []
  c <- knot [Edge () s]
  c' <- knot [Edge () s]
  p <- knot [Edge () c, Edge () c', Edge () c, Edge () c']
    // [Path [0,0], Path [1,0]]
    // [Path [2,0], Path [3,0]]
  knot [Edge () p]
    // [Path [0,0,0], Path [0,1,0]]
    // [Path [0,0], Path [0,2]]
    // [Path [0,1], Path [0,3]]

crescent' :: BAC String
crescent' = fromJust $ braid $ do
  s <- knot []
  c <- knot [Edge "cs" s]
  c' <- knot [Edge "c's" s]
  p <- knot [Edge "pc1" c, Edge "pc'1" c', Edge "pc2" c, Edge "pc'2" c']
    // [Path [0,0], Path [1,0]]
    // [Path [2,0], Path [3,0]]
  knot [Edge "0p" p]
    // [Path [0,0,0], Path [0,1,0]]
    // [Path [0,0], Path [0,2]]
    // [Path [0,1], Path [0,3]]
