-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 11

import Data.Primitives.Views
import System

-- check that all functions are total
%default total

--
-- section 11.1 (examples)
--

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith lbs [] = []
labelWith (lbl :: lbls) (val :: vals) = (lbl, val) :: labelWith lbls vals

label : List a -> List (Integer, a)
label = labelWith (iterate (+1) 0)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

partial
quiz : Stream Int -> (score : Nat) -> IO ()
quiz  (num1 :: num2 :: nums) score
  = do putStrLn ("Score so far:" ++ show score)
       putStr (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
         then do putStrLn "Correct!"
                 quiz nums (score + 1)
         else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                 quiz nums score

--
-- section 11.1 (exercises)
--

every_other : Stream Int -> Stream Int
every_other (first :: second :: rest) = second :: every_other rest

Functor InfList where
  map f (value :: xs) = f value :: map f xs

data Face = Head | Tails

partial
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips n xs = map helper $ take n xs
  where
    total
    helper : Int -> Face
    helper x with (divides x 2)
      helper ((2 * div) + rem) | (DivBy prf)
        = if rem == 0 then Head else Tails

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = approx :: (square_root_approx number next)
    where
      next = (approx + (number / approx)) / 2

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z _ _ (val :: _) = val
square_root_bound (S k) n bound (val :: xs)
  = if (abs (val * val - n)) <= bound
      then val
      else square_root_bound k n bound xs

square_root : (number : Double) -> Double
square_root n = square_root_bound 100 n 0.00000000001 (square_root_approx n n)

--
-- section 11.2 (examples)
--

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

--
-- section 11.2 (exercises)
--

totalREPL : String -> (String -> String) -> InfIO
totalREPL prompt action =
  do putStr prompt
     input <- getLine
     putStr $ action input
     totalREPL prompt action

partial
mainREPL : IO ()
mainREPL = runOnLazyFuel forever (totalREPL "\n: " toUpper)
