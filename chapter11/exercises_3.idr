-- exercises in "Type-Driven Development with Idris"
-- chapter 11, section 3, question 1

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

data Input = Answer Int
           | QuitCmd

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do res <- runCommand x
                           runCommand (f res)

run : LazyFuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit v) = pure $ Just v
run LDry (Do act gen) = pure Nothing
run (LMore fuel) (Do act gen) = do res <- runCommand act
                                   run fuel $ gen res

namespace Command
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace Console
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))

print_score : (score : Nat) -> (questions : Nat) -> String
print_score score questions
  = (show score) ++ " / " ++ (show questions)

mutual
  correct : Stream Int -> (score : Nat) -> (nb : Nat) -> ConsoleIO (Nat, Nat)
  correct nums score nb
    = do PutStr "Correct!\n"
         quiz nums (score + 1) nb

  wrong : Stream Int -> Int -> (score : Nat) -> (nb : Nat) -> ConsoleIO (Nat, Nat)
  wrong nums ans score nb
    = do PutStr $ "Wrong, the answer is " ++ show ans ++ "\n"
         quiz nums score nb

  quiz : Stream Int -> (score : Nat) -> (nb : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score nb
   = do PutStr ("Score so far: " ++ (print_score score nb) ++ "\n")
        input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
        case input of
          Answer answer => if answer == num1 * num2
                             then correct nums score (nb + 1)
                             else wrong nums (num1 * num2) score (nb + 1)
          QuitCmd => Quit (score, nb)

partial
main : IO ()
main = do seed <- time
          Just (score, nb) <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
            | Nothing => putStrLn "Ran out of fuel"
          putStrLn $ "Final score: " ++ print_score score nb

--
-- see Shell.idr
--
