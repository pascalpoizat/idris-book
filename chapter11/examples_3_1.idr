-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 11, section 3, part 1

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

data LazyFuel = LDry | LMore (Lazy LazyFuel)

partial
forever : LazyFuel
forever = LMore forever

data RunIO : Type -> Type where
  Quit : a -> RunIO a
  Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

run : LazyFuel -> RunIO a -> IO (Maybe a)
run _ (Quit value) = pure $ Just value
run LDry (Do act gen) = pure Nothing
run (LMore fuel) (Do act gen) = do res <- act
                                   run fuel $ gen res

greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
             then do putStrLn "Bye bye!"
                     Quit ()
             else do putStrLn $ "Hello " ++ name
                     greet

partial
main : IO ()
main = do run forever greet
          pure ()
