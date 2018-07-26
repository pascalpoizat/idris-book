-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 7
-- note: some solutions may be using features not presented in chapters 1-7.

--
-- section 7.1
--

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

Eq Shape where
  (==) (Triangle x z) (Triangle x' z') = x == x' && z == z'
  (==) (Rectangle x z) (Rectangle x' z') = x == x' && z == z'
  (==) (Circle x) (Circle x') = x == x'
  (==) _ _ = False

Ord Shape where
  compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]

--
-- section 7.2
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
