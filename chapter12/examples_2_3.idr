-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 12, section 2, part 3

import System
import Data.Primitives.Views

-- check that all functions are total
%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

%name GameState state, state1, state2

Show GameState where
  show s = show (correct (score s)) ++ " / " ++
           show (attempted (score s)) ++ "\n" ++
           "Difficulty: " ++ show (difficulty s)

setDifficulty : Int -> GameState -> GameState
setDifficulty k = record { difficulty = k }

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->attempted $= (+1), score->correct $= (+1) }

initState : GameState
initState = MkGameState (MkScore 0 0) 12

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

%name Command cmd, cmd1, cmd2

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand xs state (PutStr x)
  = do putStr x
       pure ((), xs, state)
runCommand xs state GetLine
  = do str <- getLine
       pure (str, xs, state)
runCommand (value :: xs) state GetRandom
  = pure (getRandom value (difficulty state), xs, state)
    where
      getRandom : Int -> Int -> Int
      getRandom val max with (divides val max)
        getRandom val 0 | DivByZero = 1
        getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand xs state GetGameState
  = pure (state, xs, state)
runCommand xs state (PutGameState state1)
  = pure ((), xs, state1)
runCommand xs state (Pure x) = pure (x, xs, state)
runCommand xs state (Bind cmd f)
  = do (res, xs', state') <- runCommand xs state cmd
       runCommand xs' state' (f res)

run : Fuel -> Stream Int -> GameState -> ConsoleIO a ->
      IO (Maybe a, Stream Int, GameState)
run fuel xs state (Quit val)
  = do pure (Just val, xs, state)
run (More fuel) xs state (Do cmd f)
  = do (res, xs', state') <- runCommand xs state cmd
       run fuel xs' state' (f res)
run Dry xs state p
  = pure (Nothing, xs, state)

data Input = Answer Int
           | QuitCmd

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               st <- GetGameState
               PutGameState (addCorrect st)
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                 st <- GetGameState
                 PutGameState (addWrong st)
                 quiz

  readInput : (prompt : String) -> Command Input
  readInput prompt = do PutStr prompt
                        answer <- GetLine
                        if toLower answer == "quit"
                          then Pure QuitCmd
                          else Pure (Answer (cast answer))

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")
            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
              Answer answer => if answer == num1 * num2
                                  then correct
                                  else wrong (num1 * num2)
              QuitCmd => Quit st

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                  (seed' `shiftR` 2) :: randoms seed'

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <-
            run forever (randoms (fromInteger seed)) initState quiz
              | _ => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show state)
