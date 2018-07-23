-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 2

-- exercise 1
val1 : (String, String, String)
val1 = ("A", "B", "C")
val2 : List String
val2 = ["A", "B", "C"]
val3 : ((String, String), String)
val3 = (("A", "B"), "C")

-- exercise 2
palindrome : String -> Bool
palindrome x = x == reverse x

-- exercise 3
palindrome2_1 : String -> Bool
palindrome2_1 x = let x' = toLower x in (x' == reverse x')

palindrome2_2 : String -> Bool
palindrome2_2 x = palindrome (toLower x)

-- exercise 4
palindrome3_1 : String -> Bool
palindrome3_1 x = case length x >= 10 of
                        False => False
                        True => palindrome2_1 x

palindrome3_2 : String -> Bool
palindrome3_2 x = if length x >= 10
                      then palindrome2_1 x
                      else False

palindrome3_3 : String -> Bool
palindrome3_3 x = (length x >= 10) && palindrome2_1 x

-- exercise 5
palindrome4_1 : Nat -> String -> Bool
palindrome4_1 n x = case length x >= n of
                        False => False
                        True => palindrome2_1 x

palindrome4_2 : Nat -> String -> Bool
palindrome4_2 n x = if length x >= n
                      then palindrome2_1 x
                      else False

palindrome4_3 : Nat -> String -> Bool
palindrome4_3 n x = (length x >= n) && palindrome2_1 x

-- exercise 6
counts : String -> (Nat, Nat)
counts str = (length (words str), length str)

-- exercise 7
top_ten : Ord a => List a -> List a
top_ten xs = take 10 (reverse (sort xs))

-- exercise 8
over_length_1 : Nat -> List String -> Nat
over_length_1 k [] = 0
over_length_1 k (x :: xs) = case length x > k of
                               False => over_length_1 k xs
                               True => 1 + over_length_1 k xs

over_length_2 : Nat -> List String -> Nat
over_length_2 k xs = length (filter lengthMoreThanK xs)
                      where
                        lengthMoreThanK : String -> Bool
                        lengthMoreThanK str = length str > k

-- exercise 9
-- run with ":exec ex9_1" or ":exec ex9_2" (or use a function main in a module Main)
ex9_1 : IO ()
ex9_1 = repl "Enter a string: " show_palindrome2_1
  where
    show_palindrome2_1 str = show (palindrome2_1 str) ++ "\n"

ex9_2 : IO ()
ex9_2 = repl "Enter a string: " show_counts
  where
    show_counts str = show (counts str) ++ "\n"
