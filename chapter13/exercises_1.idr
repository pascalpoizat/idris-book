-- exercises in "Type-Driven Development with Idris"
-- chapter 13, section 1

-- check that all functions are total
%default total

namespace exercise1

  data DoorState = DoorClosed | DoorOpen

  data DoorCmd : Type ->
                 DoorState ->
                 DoorState ->
                 Type where
    Open :     DoorCmd ()       DoorClosed DoorOpen
    Close :    DoorCmd ()       DoorOpen   DoorClosed
    RingBell : DoorCmd ()       state      state
    Pure :     ty -> DoorCmd ty state      state
    (>>=) :    DoorCmd a        state1     state2 ->
               (a -> DoorCmd b  state2     state3) ->
               DoorCmd b        state1     state3

  doorProg : DoorCmd () DoorClosed DoorClosed
  doorProg = do RingBell
                Open
                RingBell
                Close

namespace exercise2

  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S k) (k)
    Pure : ty -> GuessCmd ty state state
    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3

  threeGuesses : GuessCmd () 3 0
  threeGuesses = do Try 10
                    Try 20
                    Try 15
                    Pure ()

  -- noGuesses : GuessCmd () 0 0
  -- noGuesses = do Try 10
  --                Pure ()

namespace exercise3

  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt :     MatterCmd () Solid Liquid
    Boil :     MatterCmd () Liquid Gas
    Condense : MatterCmd () Gas Liquid
    Freeze :   MatterCmd () Liquid Solid
    Pure : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3

  iceSteam : MatterCmd () Solid Gas
  iceSteam = do Melt
                Boil

  steamIce : MatterCmd () Gas Solid
  steamIce = do Condense
                Freeze

  -- overMelt : MatterCmd () Solid Gas
  -- overMelt = do Melt
  --               Melt
