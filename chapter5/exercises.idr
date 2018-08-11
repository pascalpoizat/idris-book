-- exercises in "Type-Driven Development with Idris"
-- chapter 5

import System
import Data.Vect

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

printLonger' : IO ()
printLonger' =  putStr "First string: " >>= \_ =>
                getLine >>= \str1 =>
                putStr "Second string: " >>= \_ =>
                getLine >>= \str2 =>
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
-- > :exec test_repl
-- command: foo
-- 0> foo!
-- command: bar
-- 1> bar!
-- command: quit
-- >
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

--
-- section 5.3
--

partial
readToBlank : IO (List String)
readToBlank = do
                line <- getLine
                if line == ""
                  then pure []
                  else (do lines <- readToBlank
                           pure (line :: lines))

partial
run_readToBlank : IO ()
run_readToBlank = do
                    lines <- readToBlank
                    putStrLn $ show lines

-- version that concat lines and write them at once using writeFile
-- (writeFile opens the file in WriteTruncate mode, writes, and then closes the file)
partial
readAndSave : IO ()
readAndSave = do
               putStrLn "Enter lines: "
               lines <- readToBlank
               putStr "Filename: "
               filename <- getLine
               Right () <- writeFile filename (concat $ intersperse "\n" lines)
             | Left error => putStrLn (show error)
               putStrLn $ "lines saved to file " ++ filename

writeLinesToFile : (file : File) ->
                   (lines : List String) ->
                   IO (Either FileError ())
writeLinesToFile file [] = pure (Right ())
writeLinesToFile file (x :: xs)
  = do
      line <- pure (if isNil xs then x else x ++ "\n")
      Right () <- fPutStr file line | Left error => pure (Left error)
      writeLinesToFile file xs

-- version that writes lines one by one
-- (fPutStrLn writes a single line)
partial
readAndSave2 : IO ()
readAndSave2 = do
               putStrLn "Enter lines: "
               lines <- readToBlank
               putStr "Filename: "
               filename <- getLine
               Right file <- openFile filename WriteTruncate
             | Left error => putStrLn (show error)
               Right () <- writeLinesToFile file lines
             | Left error => putStrLn (show error)
               closeFile file
               putStrLn $ "lines saved to file " ++ filename

partial
readVectFileHelper : (file : File) -> IO (Either FileError (n ** Vect n String))
readVectFileHelper file
  = do
      False <- fEOF file | True => pure (Right (_ ** []))
      Right x <- fGetLine file | Left error => pure (Left error)
      Right (m ** xs) <- readVectFileHelper file | Left error => pure (Left error)
      pure $ Right (S m ** x :: xs)

partial
readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename
  = do
       Right file <- openFile filename Read
     | Left error => (do putStrLn (show error)
                         pure (_ ** []))
       Right dp <- readVectFileHelper file
     | Left error => (do putStrLn (show error)
                         pure (_ ** []))
       closeFile file
       pure dp
