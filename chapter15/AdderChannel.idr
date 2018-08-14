-- examples in "Type-Driven Development with Idris"
-- chapter 15, section 15.1

import System.Concurrency.Channels

-- check that all functions are total
%default total

data Message = Add Nat Nat

namespace section_15_1_2

  partial
  adder : IO ()
  adder = do Just sender_chan <- listen 1
             | Nothing => section_15_1_2.adder
             Just msg <- unsafeRecv Message sender_chan
             | Nothing => section_15_1_2.adder
             case msg of
               Add x y => do ok <- unsafeSend sender_chan (x + y)
                             section_15_1_2.adder

  partial
  main : IO ()
  main = do Just adder_id <- spawn section_15_1_2.adder
            | Nothing => putStrLn "Spawn failed"
            Just chan <- connect adder_id
            | Nothing => putStrLn "Connection failed"
            ok <- unsafeSend chan (Add 2 3)
            Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
            printLn answer

namespace section_15_1_3_pb1

  partial
  adder : IO ()
  adder = do Just sender_chan <- listen 1
             | Nothing => section_15_1_3_pb1.adder
             Just msg <- unsafeRecv Message sender_chan
             | Nothing => section_15_1_3_pb1.adder
             case msg of
               Add x y => do ok <- unsafeSend sender_chan (x + y)
                             section_15_1_3_pb1.adder

  partial
  main : IO ()
  main = do Just adder_id <- spawn section_15_1_3_pb1.adder
            | Nothing => putStrLn "Spawn failed"
            Just chan <- connect adder_id
            | Nothing => putStrLn "Connection failed"
            ok <- unsafeSend chan (Add 2 3)
            Just answer <- unsafeRecv String chan
            | Nothing => putStrLn "Send failed"
            printLn answer

namespace section_15_1_3_pb2

  partial
  adder : IO ()
  adder = do Just sender_chan <- listen 1
             | Nothing => section_15_1_3_pb2.adder
             Just msg <- unsafeRecv Message sender_chan
             | Nothing => section_15_1_3_pb2.adder
             case msg of
               Add x y => do ok <- unsafeSend sender_chan (x + y)
                             section_15_1_3_pb2.adder

  partial
  main : IO ()
  main = do Just adder_id <- spawn section_15_1_3_pb2.adder
            | Nothing => putStrLn "Spawn failed"
            Just chan <- connect adder_id
            | Nothing => putStrLn "Connection failed"
            ok <- unsafeSend chan (Add 2 3)
            Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
            printLn answer
            ok <- unsafeSend chan (Add 3 4)
            Just answer <- unsafeRecv Nat chan
            | Nothing => putStrLn "Send failed"
            printLn answer
