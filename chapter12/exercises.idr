-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 12

import Control.Monad.State
import Tree

-- check that all functions are total
%default total

--
-- section 12.1
--

update : (stateType -> stateType) -> State stateType ()
update f = get >>= put . f
-- or:
-- update f = do s <- get
--               put $ f s

increase : Nat -> State Nat ()
increase x = update (+x)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node left val right)
  = do countEmpty left
       countEmpty right

incrementFst : State (Nat, Nat) ()
incrementFst = update (\(x,y) => (x + 1, y))

incrementSnd : State (Nat, Nat) ()
incrementSnd = update (\(x,y) => (x, y + 1))

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = incrementFst
countEmptyNode (Node left val right)
  = do countEmptyNode left
       countEmptyNode right
       incrementSnd

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

--
-- section 12.3
-- see Quiz.idr (with added things to update difficulty)
-- see SocialNews.idr
--
