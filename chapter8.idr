-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 8
-- note: some solutions may be using features not presented in chapters 1-8.

-- check that all functions are total
%default total

--
-- section 8.1 (examples)
--

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

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

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 (Just (Same len)) => Just input

--
-- section 8.1 (exercices)
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
-- if the three numlbers are equal then their three successors are equal
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
