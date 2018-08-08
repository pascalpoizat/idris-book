-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 13, section 1, VendingMachine part

-- check that all functions are total
%default total

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type ->
                  VendState ->
                  VendState ->
                  Type where
  InsertCoin : MachineCmd () (pounds,     chocs) (S pounds,        chocs)
  Vend :       MachineCmd () (S pounds, S chocs) (  pounds,        chocs)
  GetCoins :   MachineCmd () (  pounds,   chocs) (       Z,        chocs)
  Refill :     (bars : Nat) ->
               MachineCmd () (       Z,   chocs) (       Z, bars + chocs)
  Display :    String ->
               MachineCmd ()                   s                        s
  GetInput :   MachineCmd (Maybe Input)        s                        s
  Pure :       ty -> MachineCmd ty             s                        s
  (>>=) :      MachineCmd a                   s1                       s2 ->
               (a -> MachineCmd b             s2                       s3) ->
               MachineCmd b                   s1                       s3

data MachineIO : VendState -> Type where
  Do : MachineCmd a s1 s2 ->
       (a -> Inf (MachineIO s2)) -> MachineIO s1

namespace MachineDo
  (>>=) : MachineCmd a s1 s2 ->
          (a -> Inf (MachineIO s2)) -> MachineIO s1
  (>>=) = Do

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
         COIN => do InsertCoin
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         REFILL num => refill num
