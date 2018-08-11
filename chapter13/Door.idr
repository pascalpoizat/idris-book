-- examples in "Type-Driven Development with Idris"
-- chapter 13, section 1, Door part

-- check that all functions are total
%default total

data DoorState = DoorClosed | DoorOpen

data DoorCmd : Type ->
               DoorState ->
               DoorState ->
               Type where
  Open :     DoorCmd ()       DoorClosed DoorOpen
  Close :    DoorCmd ()       DoorOpen   DoorClosed
  RingBell : DoorCmd ()       DoorClosed DoorClosed
  Pure :     ty -> DoorCmd ty state      state
  (>>=) :    DoorCmd a        state1     state2 ->
             (a -> DoorCmd b  state2     state3) ->
             DoorCmd b        state1     state3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              Close
