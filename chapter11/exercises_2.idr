-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 11, section 2

import Data.Primitives.Views

-- check that all functions are total
%default total

data InfIO : Type where
  Do : IO a
       -> (a -> Inf InfIO)
       -> InfIO

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

totalREPL : String -> (String -> String) -> InfIO
totalREPL prompt action =
  do putStr prompt
     input <- getLine
     putStr $ action input
     totalREPL prompt action

partial
mainREPL : IO ()
mainREPL = runOnLazyFuel forever (totalREPL "\n: " toUpper)
