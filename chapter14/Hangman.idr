-- exercises in "Type-Driven Development with Idris"
-- chapter 14, section 3, Hangman part

import Data.Vect

-- check that all functions are total
%default total

||| Remove an element in a vector
removeElem : (value : a) -> (xs : Vect (S n) a) ->
              {auto prf : Elem value xs} ->
              Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later}
  = y :: removeElem value ys

||| (Abstract) State of the game
data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState

||| Result of a guess
data GuessResult = Correct | Incorrect

||| Letters in a word
letters : String -> List Char
letters str = nub $ map toUpper $ unpack str

||| Game commands
data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
  ||| new game
  NewGame : (word : String) ->
            GameCmd () NotRunning $
                       const (Running 6 (length (letters word)))
  ||| won game
  Won : GameCmd () (Running (S guesses) 0) $
                   const NotRunning
  ||| lost game
  Lost : GameCmd () (Running 0 (S guesses)) $
                    const NotRunning
  ||| guess a letter
  Guess : (c : Char) ->
          GameCmd  GuessResult
                   (Running (S guesses) (S letters))
                   (\res => case res of
                              Correct => Running (S guesses) letters
                              Incorrect => Running guesses (S letters))
  ||| display the game state
  ShowState : GameCmd () state $ const state
  ||| display a message
  Message : String -> GameCmd () state $ const state
  ||| read a guess
  ReadGuess : GameCmd Char state $ const state
  ||| pure
  Pure : (res : ty) -> GameCmd ty (state res) state
  ||| sequence
  (>>=) : GameCmd a state1 state2 ->
          ((res : a) -> GameCmd b (state2 res) state3) ->
          GameCmd b state1 state3

namespace Loop
  ||| Game loop (type)
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    ||| sequence
    (>>=) : GameCmd a state1 state2 ->
            ((res : a) -> Inf (GameLoop b (state2 res) state3)) ->
            GameLoop b state1 state3
    ||| exit game
    Exit : GameLoop () NotRunning $ const NotRunning

||| Game loop (implementation)
gameLoop : GameLoop () (Running (S guesses) (S letters)) $ const NotRunning
gameLoop {guesses} {letters}
  = do ShowState
       g <- ReadGuess
       ok <- Guess g
       (case ok of
             Correct => case letters of
                          Z => do Won
                                  ShowState
                                  Exit
                          S k => do Message "Correct"
                                    gameLoop
             Incorrect => case guesses of
                          Z => do Lost
                                  ShowState
                                  Exit
                          S k => do Message "Incorrect"
                                    gameLoop)

||| Game set up
hangman : GameLoop () NotRunning $ const NotRunning
hangman = do NewGame "testing"
             gameLoop

||| (Concrete) Game state
data Game : GameState -> Type where
  GameStart : Game NotRunning
  GameWon : (word : String) -> Game NotRunning
  GameLost : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) ->
               (missing : Vect letters Char) ->
               Game (Running guesses letters)

||| Game representation
Show (Game gs) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing)
    = "\n" ++ pack (map hideMissing (unpack word))
           ++ "\n" ++ show guesses ++ " guesses left"
    where hideMissing : Char -> Char
          hideMissing c = if c `elem` missing then '-' else c

||| Fuel machinery
data Fuel = Dry | More (Lazy Fuel)

||| Result of a game
data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (outstate res) ->
       GameResult ty outstate
  OutOfFuel : GameResult ty outstate

||| Helper for returns of runs
ok : (res : ty) -> Game (outstate res) -> IO (GameResult ty outstate)
ok res st = pure (OK res st)

||| Running a game command over fuel
partial
runCmd : Fuel ->
         Game instate ->
         GameCmd ty instate outstate ->
         IO (GameResult ty outstate)
runCmd fuel state (NewGame word)
  = ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd fuel (InProgress word _ missing) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ missing) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c)
  = case isElem c missing of
      Yes prf => ok Correct (InProgress word _ (removeElem c missing))
      No contra => ok Incorrect (InProgress word _ missing)
runCmd fuel state ShowState = do printLn state
                                 ok () state
runCmd fuel state (Message x) = do putStrLn x
                                   ok () state
runCmd fuel state ReadGuess
  = do putStr "Guess: "
       input <- getLine
       case unpack input of
         [x] => if isAlpha x
                  then ok (toUpper x) state
                  else do putStrLn "Invalid input"
                          runCmd fuel state ReadGuess
         _ => do putStrLn "Invalid input"
                 runCmd fuel state ReadGuess
runCmd Dry _ _ = pure OutOfFuel
runCmd fuel state (Pure res) = ok res state
runCmd fuel st (cmd >>= next)
  = do OK cmdRes newSt <- runCmd fuel st cmd
        | OutOfFuel => pure OutOfFuel
       runCmd fuel newSt (next cmdRes)

||| Running a game loop over fuel
partial
run : Fuel ->
      Game instate ->
      GameLoop ty instate outstate ->
      IO (GameResult ty outstate)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (cmd >>= next)
  = do OK cmdRes newSt <- runCmd fuel st cmd
       | OutOfFuel => pure OutOfFuel
       run fuel newSt (next cmdRes)
run (More fuel) st Exit = ok () st

-- all remaining functions are partial
%default partial

forever : Fuel
forever = More forever

main : IO ()
main = do run forever GameStart hangman
          pure ()
