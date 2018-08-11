-- examples in "Type-Driven Development with Idris"
-- chapter 14, section 1, Door part

-- check that all functions are total
%default total

data DoorResult = OK | Jammed

data DoorState = DoorClosed | DoorOpen

data DoorCmd : (ty : Type) ->
               DoorState ->
               (ty -> DoorState) ->
               Type where
  Open :                   DoorCmd DoorResult DoorClosed
                                              (\res => case res of
                                                        OK => DoorOpen
                                                        Jammed => DoorClosed)
  Close :                  DoorCmd ()         DoorOpen      (const DoorClosed)
  RingBell :               DoorCmd ()         DoorClosed    (const DoorClosed)
  Display :  String ->     DoorCmd ()         state         (const state)
  Pure :     (res : ty) -> DoorCmd ty         (state res)   state
  (>>=) :                  DoorCmd a          state1        state2 ->
             ((res : a) -> DoorCmd b          (state2 res)  state3) ->
                           DoorCmd b          state1        state3

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "Door Jammed"
              Display "Door OK"
              Close

logOpen : DoorCmd DoorResult DoorClosed
                             (\res => case res of
                                        OK => DoorOpen
                                        Jammed => DoorClosed)
logOpen = do Display "Trying to open the door"
             OK <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             Pure OK
