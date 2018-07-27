-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 8
-- note: some solutions may be using features not presented in chapters 1-8.

import Data.Vect

-- check that all functions are total
%default total

--
-- section 8.1 (examples)
--

data Vector : Nat -> Type -> Type where
  Nil : Vector Z a
  (::) : a -> Vector k a -> Vector (S k) a

-- exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLength {m} len input = case m == len of
--                                  False => Nothing
--                                  True => Just ?exactLength_rhs_2

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = checkEqNat k j >>= Just . (sameS _ _)

exactLength : (len : Nat) -> (input : Vector m a) -> Maybe (Vector len a)
exactLength {m} len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 (Just (Same len)) => Just input

--
-- section 8.1 (exercises)
--

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

-- *chapter8> allSameS 2 3 2 Same3
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
-- *chapter8> allSameS 2 2 2 Same3
-- Same3 : ThreeEq 3 3 3

--
-- section 8.2 (examples)
--

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs)
  = let result = myReverse xs ++ [x] in
        rewrite plusCommutative 1 k in result

reverse_proof : (x : elem) -> (xs : Vect len elem) ->
                Vect (len + 1) elem -> Vect (S len) elem
reverse_proof {len} x xs result = rewrite plusCommutative 1 len in result

myReverse' : Vect n elem -> Vect n elem
myReverse' [] = []
myReverse' (x :: xs) = reverse_proof x xs (myReverse' xs ++ [x])

append_nil : (ys : Vect m elem) ->
             Vect (plus m 0) elem
append_nil {m} ys = rewrite plusZeroRightNeutral m in ys

append_xs : Vect (S (m + len)) elem -> Vect (plus m (S len)) elem
append_xs {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend [] ys = append_nil ys
myAppend (x :: xs) ys = append_xs (x :: myAppend xs ys)

--
-- section 8.2 (exercises)
--

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite sym (plusZeroRightNeutral m) in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in
                         rewrite plusSuccRightSucc m k in Refl

reverseProof_nil : Vect n1 a -> Vect (plus n1 0) a
reverseProof_nil {n1} xs = rewrite plusZeroRightNeutral n1 in xs

reverseProof_xs : Vect (S (plus n1 len)) a -> Vect (plus n1 (S len)) a
reverseProof_xs {n1} {len} xs = rewrite sym (plusSuccRightSucc n1 len) in xs

myReverse'' : Vect n a -> Vect n a
myReverse'' xs = reverse' [] xs
  where
    reverse' : Vect n a -> Vect m a -> Vect (n+m) a
    reverse' acc [] = reverseProof_nil acc
    reverse' acc (x :: xs) = reverseProof_xs (reverse' (x :: acc) xs)

--
-- section 8.3 (examples)
--

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSucc : x = S x -> Void
valueNotSucc Refl impossible

zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

succNotZero : (S k = 0) -> Void
succNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat2 : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat2 Z Z = Yes Refl
checkEqNat2 Z (S k) = No zeroNotSucc
checkEqNat2 (S k) Z = No succNotZero
checkEqNat2 (S k) (S j) = case checkEqNat2 k j of
                               (Yes prf) => Yes (cong prf)
                               (No contra) => No (noRec contra)

exactLength2 : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength2 {m} len input = case decEq m len of
                                  (Yes Refl) => Just input
                                  (No contra) => Nothing

--
-- section 8.3 (exercises)
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
