-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 11, section 2

import Data.Primitives.Views
import System

-- check that all functions are total
%default total

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

data InfIO : Type where
  Do : IO a
       -> (a -> Inf InfIO)
       -> InfIO

loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg)
                   (\_ => loopPrint msg)

partial
run : InfIO -> IO ()
run (Do action cont) = do res <- action
                          run (cont res)

data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

runOnFuel : Fuel -> InfIO -> IO ()
runOnFuel (More fuel) (Do act gen) = do res <- act
                                        runOnFuel fuel (gen res)
runOnFuel Dry ios = putStrLn "Out of fuel"

data LazyFuel = LDry | LMore (Lazy LazyFuel)

partial
forever : LazyFuel
forever = LMore forever

runOnLazyFuel : LazyFuel -> InfIO -> IO ()
runOnLazyFuel (LMore fuel) (Do act gen) = do res <- act
                                             runOnLazyFuel fuel (gen res)
runOnLazyFuel LDry ios = putStrLn "Out of fuel"

(>>=) : IO a -> (a -> Inf InfIO)  -> InfIO
(>>=) = Do

loopPrint' : String -> InfIO
loopPrint' msg = do putStrLn msg
                    loopPrint' msg

quiz' : Stream Int -> (score : Nat) -> InfIO
quiz'  (num1 :: num2 :: nums) score
  = do putStrLn ("Score so far:" ++ show score)
       putStr (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
         then do putStrLn "Correct!"
                 quiz' nums (score + 1)
         else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                 quiz' nums score

partial
main : IO ()
main = do seed <- time
          runOnLazyFuel forever (quiz' (arithInputs (fromInteger seed)) 0)
