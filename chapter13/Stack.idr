-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 13, section 2, Stack part

import Data.Vect

-- check that all functions are total
%default total

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)
  Pure : ty -> StackCmd ty s s
  (>>=) : StackCmd a s1 s2 ->
          (a -> StackCmd b s2 s3) ->
          StackCmd b s1 s3

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           (ty, Vect outHeight Integer)
runStack stk (Push x) = ((), x :: stk)
runStack (x :: xs) Pop = (x, xs)
runStack (x :: xs) Top = (x, x :: xs)
runStack stk (Pure x) = (x, stk)
runStack stk (x >>= f)
  = let (res, stk') = runStack stk x in
      runStack stk' (f res)

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push $ val1 + val2
