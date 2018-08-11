-- examples in "Type-Driven Development with Idris"
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

-- exactLength : (len : Nat) -> (input : Vector m a) -> Maybe (Vector len a)
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
-- section 8.2
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
-- section 8.3
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
