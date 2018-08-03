-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 8

import Data.Vect

-- check that all functions are total
%default total

--
-- section 8.1
--

data Vector : Nat -> Type -> Type where
  Nil : Vector Z a
  (::) : a -> Vector k a -> Vector (S k) a

same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  Same3 : ThreeEq n n n

-- for all three natural numbers,
-- if the three numbers are equal then their three successors are equal
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z Same3 = Same3

-- > allSameS 2 3 2 Same3
-- (input):1:1-20:When checking an application of function Main.allSameS:
--         Type mismatch between
--                 ThreeEq n n n (Type of Same3)
--         and
--                 ThreeEq 2 3 2 (Expected type)
--
--         Specifically:
--                 Type mismatch between
--                         0
--                 and
--                         1
-- > allSameS 2 2 2 Same3
-- Same3 : ThreeEq 3 3 3

--
-- section 8.2
--

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite sym (plusZeroRightNeutral m) in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in
                         rewrite plusSuccRightSucc m k in Refl

reverseProof_nil : Vect n1 a -> Vect (plus n1 0) a
reverseProof_nil {n1} xs = rewrite plusZeroRightNeutral n1 in xs

reverseProof_xs : Vect (S (plus n1 len)) a -> Vect (plus n1 (S len)) a
reverseProof_xs {n1} {len} xs = rewrite sym (plusSuccRightSucc n1 len) in xs

myReverse : Vect n a -> Vect n a
myReverse xs = reverse [] xs
  where
    reverse : Vect n a -> Vect m a -> Vect (n+m) a
    reverse acc [] = reverseProof_nil acc
    reverse acc (x :: xs) = reverseProof_xs (reverse (x :: acc) xs)

--
-- section 8.3
--

headUnequal : DecEq a => {xs : Vector n a} -> {ys : Vector n a} ->
              (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vector n a} -> {ys : Vector n a} ->
              (contra : (xs = ys) -> Void) -> ((x :: xs) = (x :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vector n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys)
    = case decEq x y of
        Yes Refl => case decEq xs ys of
                      Yes Refl => Yes Refl
                      No contra2 => No (tailUnequal contra2)
        No contra => No (headUnequal contra)
