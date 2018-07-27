-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 7
-- note: some solutions may be using features not presented in chapters 1-7.

-- check that all functions are total
%default total

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

--
-- section 7.3 (examples)
--

data BST elem = Empty
              | Node (BST elem) elem (BST elem)

-- from Haskell's Data.Tree
shift : String -> String -> List String -> List String
shift str1 str2 strings
  = zipWith (++) (take (length strings) $ str1 :: repeat str2) strings

-- from Haskell's Data.Tree
partial
draw : Show elem => BST elem -> List String
draw Empty = ["*"]
draw (Node left x right) = (show x) :: helper [left, right]
where
  partial
  helper : List (BST elem) -> List String
  helper [] = []
  helper (t :: []) = "|" :: shift "`- " "   " (draw t)
  helper (t :: ts) = "|" :: shift "+- " "|  " (draw t) ++ helper ts

-- from Haskell's Data.Tree
partial
drawTree : Show elem => BST elem -> String
drawTree = unlines . draw

partial
Show elem => Show (BST elem) where
  show x = drawTree x

insert : Ord elem => elem -> BST elem -> BST elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
 = case compare x val of
     LT => Node (insert x left) val right
     EQ => orig
     GT => Node left val (insert x right)

listToTree : Ord a => List a -> BST a
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

treeToList : BST a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right

Functor BST where
  map func Empty = Empty
  map func (Node left val right) =
    Node (map func left) (func val) (map func right)

-- we have two alternatives to implement Foldable for BST
-- one here: following https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html
-- one in chapter 7 of the book
--
-- *chapter7> :let tree = listToTree [1,4,6,7,3]
-- *chapter7> foldr (::) [] tree
-- [1, 3, 4, 6, 7] : List Integer
-- *chapter7> foldl (\x,y => x ++ [y]) [] tree
-- [1, 3, 4, 6, 7] : List Integer
--
-- *chapter7> foldr @{chapter} (::) [] tree
-- [3, 7, 6, 4, 1] : List Integer
-- *chapter7> foldl @{chapter} (\x,y => x ++ [y]) [] tree
-- [3, 7, 6, 4, 1] : List Integer

-- following https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html
-- foldr func (func e (foldr func acc right)) left
--
Foldable BST where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let rightVal = foldr func acc right
        eVal = func e rightVal
    in
        foldr func eVal left

-- following the chapter
-- func e (foldr func (foldr func acc left) right)
--
[chapter] Foldable BST where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let leftVal = foldr func acc left
        rightVal = foldr func leftVal right
    in
        func e rightVal

-- call with:
-- *chapter7> :exec printTree $ listToTree [1,4,6,3,7]
-- 7
-- |
-- +- 3
-- |  |
-- |  +- 1
-- |  |  |
-- |  |  +- *
-- |  |  |
-- |  |  `- *
-- |  |
-- |  `- 6
-- |     |
-- |     +- 4
-- |     |  |
-- |     |  +- *
-- |     |  |
-- |     |  `- *
-- |     |
-- |     `- *
-- |
-- `- *
partial
printTree : Show elem => (BST elem) -> IO ()
printTree t = do putStrLn (show t)

--
-- section 7.3 (exercises)
--

Functor Expr where
  map func (Val x) = Val $ func x
  map func (Add x y) = Add (map func x) (map func y)
  map func (Sub x y) = Sub (map func x) (map func y)
  map func (Mul x y) = Mul (map func x) (map func y)
  map func (Div x y) = Div (map func x) (map func y)
  map func (Abs x) = Abs $ map func x

-- we define Vect by hand (here renamed Vector)
data Vector : (size : Nat) -> (ty : Type) -> Type where
  Nil : Vector Z ty
  (::) : (x : ty) -> (xs : Vector size ty) -> Vector (S size) ty

Eq ty => Eq (Vector n ty) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = (x == y) && xs == ys
  (==) _ _ = False

Foldable (Vector n) where
  foldr func init [] = init
  foldr func init (x :: xs) = func x (foldr func init xs)
