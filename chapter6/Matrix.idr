-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 6

import Data.Vect

-- check that all functions are total
%default total

Matrix : (rows : Nat) -> (cols : Nat) -> Type -> Type
Matrix n m t = Vect n (Vect m t)

testMatrix : Matrix 2 3 Double
testMatrix = [[0,0,0],[0,0,0]]

-- for the fun, we rewrite the examples from chapter 3

createEmptyVector : Matrix n 0 t
createEmptyVector {n} = replicate n []

transposeMatrix : Matrix m n t -> Matrix n m t
transposeMatrix [] = createEmptyVector
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                                zipWith (::) x xsTrans

addVector : Num t => Vect n t -> Vect n t -> Vect n t
addVector = zipWith (+)

multVector : Num t => Vect n t -> Vect n t -> t
multVector xs ys = sum $ zipWith (*) xs ys

addMatrix : Num t => Matrix m n t -> Matrix m n t -> Matrix m n t
addMatrix = zipWith (addVector)

multMatrixHelper2 : Num t => Vect n t -> Matrix p n t -> Vect p t
multMatrixHelper2 x ys = map (multVector x) ys

multMatrixHelper : Num t => Matrix m n t -> Matrix p n t -> Matrix m p t
multMatrixHelper xs ys = map (flip multMatrixHelper2 $ ys) xs

multMatrix : Num t => Matrix m n t -> Matrix n p t -> Matrix m p t
multMatrix xs ys = multMatrixHelper xs $ transposeMatrix ys

v1 : Matrix 3 2 Nat
v1 = [[1,2],[3,4],[5,6]]

v2 : Matrix 2 4 Nat
v2 = [[7,8,9,10],[11,12,13,14]]

v1v1 : Matrix 3 2 Nat
v1v1 = addMatrix v1 v1
-- v1v1 : Matrix 3 2 Nat
-- [[2, 4], [6, 8], [10, 12]] : Vect 3 (Vect 2 Nat)

v1v2 : Matrix 3 4 Nat
v1v2 = multMatrix v1 v2
-- v1v2 : Matrix 3 4 Nat
-- [[29, 32, 35, 38], [65, 72, 79, 86], [101, 112, 123, 134]] : Vect 3 (Vect 4 Nat)

-- we get nice error messages
--
-- > addMatrix v1 v2
-- (input):1:1-15:When checking an application of function Main.addMatrix:
--         Type mismatch between
--                 Matrix 2 4 Nat (Type of v2)
--         and
--                 Matrix 3 2 Nat (Expected type)
-- > multMatrix v1 v1
-- (input):1:1-16:When checking an application of function Main.multMatrix:
--         Type mismatch between
--                 Matrix 3 2 Nat (Type of v1)
--         and
--                 Matrix 2 p Nat (Expected type)
