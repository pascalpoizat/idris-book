-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 13, section 2

import Data.Vect

-- check that all functions are total
%default total

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)
  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height
  Pure : ty -> StackCmd ty s s
  (>>=) : StackCmd a s1 s2 ->
          (a -> StackCmd b s2 s3) ->
          StackCmd b s1 s3

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do (res, stk') <- runStack stk x
                            runStack stk' (f res)
runStack stk GetStr = do val <- getLine
                         pure (val, stk)
runStack stk (PutStr val) = do putStr val
                               pure ((), stk)

doBinOp : (Integer -> Integer -> Integer) -> StackCmd () (S (S height)) (S height)
doBinOp op = do val1 <- Pop
                val2 <- Pop
                Push $ op val1 val2

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push $ -val

doDiscard : StackCmd () (S height) (height)
doDiscard = do val <- Pop
               Pure ()

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = do val <- Top
                 Push val

data StackIO : Nat -> Type where
  Do : StackCmd a h1 h2 ->
       (a -> Inf (StackIO h2)) -> StackIO h1

namespace StackDo
  (>>=) : StackCmd a h1 h2 ->
          (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect h Integer -> StackIO h -> IO ()
run (More fuel) stk (Do c f)
  = do (res, stk') <- runStack stk c
       run fuel stk' (f res)
run Dry stk p = pure ()

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard
              | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput x = if all isDigit (unpack x)
                then Just (Number (cast x))
                else Nothing

mutual
  tryBinOp : (op : Integer -> Integer -> Integer) -> StackIO h
  tryBinOp {h = (S (S k))} op
    = do (doBinOp op)
         result <- Top
         PutStr (show result ++ "\n")
         stackCalc
  tryBinOp _
    = do PutStr "Fewer than two items on the stack\n"
         stackCalc

  tryNegate : StackIO h
  tryNegate {h = (S k)}
   = do doNegate
        result <- Top
        PutStr (show result ++ "\n")
        stackCalc
  tryNegate
   = do PutStr "Fewer than one item on the stack\n"
        stackCalc

  tryDiscard : StackIO h
  tryDiscard {h = (S k)}
   = do result <- Top
        doDiscard
        PutStr ("Discarded " ++ show result ++ "\n")
        stackCalc
  tryDiscard
   = do PutStr "Fewer than one item on the stack\n"
        stackCalc

  tryDuplicate : StackIO h
  tryDuplicate {h = (S k)}
   = do doDuplicate
        result <- Top
        PutStr ("Duplicated " ++ show result ++ "\n")
        stackCalc
  tryDuplicate
   = do PutStr "Fewer than one item on the stack\n"
        stackCalc

  stackCalc : StackIO h
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                   Nothing => do PutStr "Invalid input\n"
                                 stackCalc
                   Just (Number x) => do Push x
                                         stackCalc
                   Just Add => tryBinOp (+)
                   Just Subtract => tryBinOp (flip (-))
                   Just Multiply => tryBinOp (*)
                   Just Negate => tryNegate
                   Just Discard => tryDiscard
                   Just Duplicate => tryDuplicate

partial
main : IO ()
main = run forever [] stackCalc
