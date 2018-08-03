-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 4

-- check that all functions are total
%default total

--
-- Expressions
--

||| An integer arithmetic expression
data Expr = ||| A single integer
            Value Int
          | ||| Addition of an expression to an expression
            Addition Expr Expr
          | ||| Subtraction of an expression from an expression
            Subtraction Expr Expr
          | ||| Multiplication of an expression with an expression
            Multiplication Expr Expr

||| Evaluate an expression
evaluate : Expr -> Int
evaluate (Value x) = x
evaluate (Addition x y) = evaluate x + evaluate y
evaluate (Subtraction x y) = evaluate x - evaluate y
evaluate (Multiplication x y) = evaluate x * evaluate y
