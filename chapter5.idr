-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 5
-- note: some solutions may be using features not presented in chapters 1-5.

import System

-- check that all functions are total
%default total

--
-- section 5.1
--

printLonger : IO ()
printLonger = do putStr "First string: "
                 str1 <- getLine
                 putStr "Second string: "
                 str2 <- getLine
                 putStrLn $ show (longer str1 str2)
              where
                   longer : String -> String -> Nat
                   longer s1 s2 = max (length s1) (length s2)
--
-- section 5.2
--

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure (Just (cast input))
    else pure Nothing

partial
guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses =
  do
    putStr "Enter a number: "
    Just try <- readNumber
  | Nothing => (do putStrLn "wrong number"
                   guess target guesses)
    case compare try target of
          LT => (do putStrLn "too small"
                    guess target (S guesses))
          GT => (do putStrLn "too big"
                    guess target (S guesses))
          EQ => putStrLn ("you win in " ++ show guesses ++ " tries!")

partial
random : Nat -> IO Nat
random k = do raw <- time
              pure $ mod (fromIntegerNat . abs $ raw) k

partial
main : IO ()
main = random 100 >>= (flip guess) 1
-- or:
-- main = do target <- random 100
--           guess target 1

-- can be tested using:
-- *chapter5> :exec test_repl
-- command: foo
-- 0> foo!
-- command: bar
-- 1> bar!
-- command: quit
-- *chapter5>
partial
my_replWith : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
my_replWith state invite f =
  do putStr invite
     input <- getLine
     Just (output, state') <- pure (f state input)
   | Nothing => pure ()
     putStr output
     my_replWith state' invite f

partial
my_repl : String -> (String -> String) -> IO ()
my_repl invite f = my_replWith () invite f'
  where
    f' : a -> String -> Maybe (String, a)
    f' state input = Just (f input, state)

partial
test_repl : IO ()
test_repl = my_replWith 0
                        "command: "
                        (\s,x => if x=="quit"
                                  then Nothing
                                  else Just ((show s) ++ "> " ++ x ++ "!\n", S s))
