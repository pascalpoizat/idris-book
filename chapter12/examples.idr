-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 12

import Control.Monad.State
import Tree

-- check that all functions are total
%default total

--
-- section 12.1
--

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

namespace WithoutState

  treeLabelWith : Stream labelType -> Tree a ->
                  (Stream labelType, Tree (labelType, a))
  treeLabelWith lbs Empty = (lbs, Empty)
  treeLabelWith lbs (Node left val right)
    = let (lblthis :: lbsleft, lblleft) = treeLabelWith lbs left
          (lbsright, lblright) = treeLabelWith lbsleft right
          in
          (lbsright, Node lblleft (lblthis, val) lblright)

  treeLabel : Tree a -> Tree (Integer, a)
  treeLabel t = snd (treeLabelWith [1..] t)

namespace WithState

  treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
  treeLabelWith Empty = pure Empty
  treeLabelWith (Node left val right)
    = do lblleft <- treeLabelWith left
         (lblthis :: rest) <- get
         put rest
         lblright <- treeLabelWith right
         pure (Node lblleft (lblthis, val) lblright)

  treeLabel : Tree a -> Tree (Integer, a)
  treeLabel t = evalState (treeLabelWith t) [1..]

-- > :exec putStr $ show $ WithoutState.treeLabel testTree
-- (4, "Alice")
-- |
-- +- (2, "Fred")
-- |  |
-- |  +- (1, "Jim")
-- |  |  |
-- |  |  +- *
-- |  |  |
-- |  |  `- *
-- |  |
-- |  `- (3, "Sheila")
-- |     |
-- |     +- *
-- |     |
-- |     `- *
-- |
-- `- (5, "Bob")
--    |
--    +- *
--    |
--    `- (6, "Eve")
--       |
--       +- *
--       |
--       `- *
