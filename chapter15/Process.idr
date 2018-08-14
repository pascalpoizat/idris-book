-- examples in "Type-Driven Development with Idris"
-- chapter 15, section 15.2

import System.Concurrency.Channels

-- check that all functions are total
%default total

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where
  Action : IO a -> Process a
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
  Loop : Inf (Process a) -> Process a

partial
run : Process t -> IO t
run (Action act) = act
run (Pure val) = pure val
run (act >>= next) = do x <- run act
                        run (next x)
run (Spawn proc) = do Just pid <- spawn (run proc)
                      | Nothing => pure Nothing
                      pure (Just (MkMessage pid))
run (Request (MkMessage pid) msg)
  = do Just chan <- connect pid
       | _ => pure Nothing
       ok <- unsafeSend chan msg
       if ok then do Just x <- unsafeRecv Nat chan
                     | Nothing => pure Nothing
                     pure (Just x)
              else pure Nothing
run (Respond calc)
  = do Just sender <- listen 1
       | Nothing => pure Nothing
       Just msg <- unsafeRecv Message sender
       | Nothing => pure Nothing
       res <- run (calc msg)
       unsafeSend sender res
       pure (Just msg)
run (Loop act) = run act

procAdder : Process ()
procAdder = do Respond (\msg => case msg of
                                  Add x y => Pure (x + y))
               Loop procAdder

procMain : Process ()
procMain = do Just adder_id <- Spawn procAdder
              | Nothing => Action (putStrLn "Spawn failed")
              Just answer <- Request adder_id (Add 2 3)
              | Nothing => Action (putStrLn "Request failed")
              Action (printLn answer)

-- run with:
-- :exec run procMain
