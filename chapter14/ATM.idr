-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 14, section 2, ATM part
-- some variations wrt the book (since it has been done from scratch partly as an exercise)

import Data.Vect

-- check that all functions are total
%default total

PIN : Type
PIN = Vect 4 Char

data CheckPINResult = CorrectPIN | IncorrectPIN

data ATMState = Ready | CardInserted | Session
data HasCard : ATMState -> Type where
  HasCardInserted : HasCard CardInserted
  HasCardSession : HasCard Session

data ATMCommand : (ty : Type) ->
                  ATMState ->
                  (ty -> ATMState) ->
                  Type where
  InsertCard : ATMCommand () Ready (const CardInserted)
  EjectCard : {auto prf : HasCard state} -> ATMCommand () state (const Ready)
  GetPIN : ATMCommand PIN CardInserted (const CardInserted)
  CheckPIN : PIN -> ATMCommand CheckPINResult CardInserted
                                       (\res => case res of
                                                  CorrectPIN => Session
                                                  IncorrectPIN => CardInserted)
  GetAmount : ATMCommand Nat state (const state)
  Dispense : (amount : Nat) -> ATMCommand () Session (const Session)
  Message : (msg : String) -> ATMCommand () state (const state)
  Pure : (res : ty) -> ATMCommand ty (state res) state
  (>>=) : ATMCommand a state1 state2 ->
          ((res : a) -> ATMCommand b (state2 res) state3) ->
          ATMCommand b state1 state3

atm : ATMCommand () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         cash <- GetAmount
         Message "Checking card"
         CorrectPIN <- CheckPIN pin
         | IncorrectPIN => do Message "Incorrect PIN"
                              EjectCard
                              Message "Please take card"
         Dispense cash
         EjectCard
         Message "Please take card and cash"

testPIN : Vect 4 Char
testPIN = ['1','2','3','4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do discard <- getLine
                pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure (ch :: chs)

-- execute using
-- :exec runATM atm
runATM : ATMCommand res inState outState -> IO res
runATM InsertCard = do putStrLn "Please insert your card (press enter)"
                       x <- getLine
                       pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN = do putStr "Enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                          then pure CorrectPIN
                          else pure IncorrectPIN
runATM GetAmount = do putStr "How much would you like? "
                      x <- getLine
                      pure (cast x)
runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM (f x')
