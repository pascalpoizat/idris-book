-- exercises in "Type-Driven Development with Idris"
-- chapter 7

-- check that all functions are total
%default total

--
-- section 7.1
-- see Shape.idr
--

--
-- section 7.2
-- see Expr.idr
--

--
-- section 7.3
-- see Expr.idr
--

-- we define Vect by hand because Eq and Foldable already exist for Data.Vect
data Vect : (size : Nat) -> (ty : Type) -> Type where
  Nil : Vect Z ty
  (::) : (x : ty) -> (xs : Vect size ty) -> Vect (S size) ty

Eq ty => Eq (Vect n ty) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = (x == y) && xs == ys
  (==) _ _ = False

Foldable (Vect n) where
  foldr func init [] = init
  foldr func init (x :: xs) = func x (foldr func init xs)
