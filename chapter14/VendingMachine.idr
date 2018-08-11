-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 14, section 2, VendingMachine part

import System
import Data.Primitives.Views

-- check that all functions are total
%default total

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

strToInput : String -> Maybe Input
strToInput "insert" = Just COIN
strToInput "vend" = Just VEND
strToInput "change" = Just CHANGE
strToInput x = if all isDigit (unpack x)
                then Just (REFILL (cast x))
                else Nothing

data CoinResult = Inserted | Rejected

data MachineCmd : (ty : Type) ->
                  VendState ->
                  (ty -> VendState) ->
                  Type where
  InsertCoin : MachineCmd CoinResult (pounds, chocs)
                                     (\res => case res of
                                                Inserted => (S pounds, chocs)
                                                Rejected => (pounds, chocs))
  Vend :       MachineCmd () (S pounds, S chocs) $ const (pounds, chocs)
  GetCoins :   MachineCmd () (pounds, chocs)     $ const (Z, chocs)
  Refill :     (bars : Nat) ->
               MachineCmd () (Z, chocs)          $ const (Z, bars + chocs)
  Display :    String ->
               MachineCmd () s                   $ const s
  GetInput :   MachineCmd (Maybe Input) s        $ const s
  Pure :       (res : ty) -> MachineCmd ty (s res) s
  (>>=) :      MachineCmd a s1                     s2 ->
               ((res : a) -> MachineCmd b (s2 res) s3) ->
               MachineCmd b s1                     s3

data MachineIO : VendState -> Type where
  Do : MachineCmd a s1 s2 ->
       ((res : a) -> Inf (MachineIO (s2 res))) -> MachineIO s1

namespace MachineDo
  (>>=) : MachineCmd a s1 s2 ->
          ((res : a) -> Inf (MachineIO (s2 res))) -> MachineIO s1
  (>>=) = Do

getRandom : Int -> Int -> Int
getRandom val max with (divides val max)
  getRandom val 0 | DivByZero = 0
  getRandom ((max * div) + rem) max | (DivBy prf) = abs rem

||| "randomly generates" a valid or invalid coin
randomCoin : IO CoinResult
randomCoin = do seed <- time
                case (getRandom (fromInteger seed) 4) of
                  0 => pure Rejected
                  _ => pure Inserted

runMachine : MachineCmd ty inState outState -> IO ty
runMachine InsertCoin = do Inserted <- randomCoin
                           | Rejected => do putStrLn "bad coin"
                                            pure Rejected
                           putStrLn "good coin"
                           pure Inserted
runMachine Vend = putStrLn "Please take your chocolate"
runMachine {inState = (pounds, _)} GetCoins = putStrLn $ (show pounds) ++ " coins returned"
runMachine (Refill bars) = putStrLn $ "Chocolate remaining: " ++ (show bars)
runMachine (Display x) = putStrLn x
runMachine {inState = (pounds, bars)} GetInput
  = do putStrLn $ "Coins: " ++ (show pounds) ++ "; " ++
                  "Stock: " ++ (show bars)
       putStr "> "
       x <- getLine
       pure (strToInput x)
runMachine (Pure x) = pure x
runMachine (x >>= f) = do x' <- runMachine x
                          runMachine (f x')

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> MachineIO state -> IO ()
run (More fuel) (Do c f)
     = do res <- runMachine c
          run fuel (f res)
run Dry p = pure ()

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop
  vend {pounds = (S k)} {chocs = (S j)} = do Vend
                                             Display "Enjoy!"
                                             machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill {pounds = (S k)} num = do Display "Cannot refill: Coins in machine"
                                   machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop =
    do Just x <- GetInput
        | Nothing => do Display "Invalid input"
                        machineLoop
       case x of
         COIN => do Inserted <- InsertCoin | Rejected => do Display "Coin rejected"
                                                            machineLoop
                    Display "Coin inserted"
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         REFILL num => refill num

partial
main : IO ()
main = run forever (machineLoop { pounds = 0 } { chocs = 1} )
