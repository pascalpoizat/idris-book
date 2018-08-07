-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 12, section 2, part 1

import Tree

-- check that all functions are total
%default total

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()
  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right)
  = do lblleft <- treeLabelWith left
       (lblthis :: rest) <- get
       put rest
       lblright  <- treeLabelWith right
       pure (Node lblleft (lblthis, val) lblright)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst (runState (treeLabelWith tree) [1..])
