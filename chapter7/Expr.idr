-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 7

-- check that all functions are total
%default total

--
-- Expressions
--
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num, Abs num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num num => Num (Expr num) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg num => Neg (Expr num) where
  negate x = 0 - x
  (-) = Sub

Abs num => Abs (Expr num) where
  abs = Abs

showHelper : Show a => String -> a -> a -> String
showHelper op x y = "(" ++ show x ++ op ++ show y ++ ")"

Show num => Show (Expr num) where
  show (Val x) = show x
  show (Add x y) = showHelper " + " x y
  show (Sub x y) = showHelper " - " x y
  show (Mul x y) = showHelper " * " x y
  show (Div x y) = showHelper " `div`" x y
  show (Abs x) = "(" ++ "abs " ++ show x ++ ")"

(Neg num, Integral num, Abs num, Eq num) => Eq (Expr num) where
  (==) x y = (eval x) == (eval y)

(Neg num, Integral num, Abs num) => Cast (Expr num) num where
  cast orig = eval orig

Functor Expr where
  map func (Val x) = Val $ func x
  map func (Add x y) = Add (map func x) (map func y)
  map func (Sub x y) = Sub (map func x) (map func y)
  map func (Mul x y) = Mul (map func x) (map func y)
  map func (Div x y) = Div (map func x) (map func y)
  map func (Abs x) = Abs $ map func x
