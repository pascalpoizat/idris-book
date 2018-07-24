-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 5
-- note: some solutions may be using features not presented in chapters 1-5.

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
