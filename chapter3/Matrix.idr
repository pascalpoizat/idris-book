-- exercises in "Type-Driven Development with Idris"
-- chapter 3

import Data.Vect

-- check that all functions are total
%default total

createEmptyVector : Num t =>
                    Vect n (Vect 0 t)
createEmptyVector {n} = replicate n []
-- or:
-- createEmptyVector = replicate _ []

transposeHelper : Num t =>
                  Vect n t ->
                  Vect n (Vect k t) ->
                  Vect n (Vect (S k) t)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMatrix : Num t =>
                  Vect m (Vect n t) ->
                  Vect n (Vect m t)
transposeMatrix [] = createEmptyVector
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                            transposeHelper x xsTrans

transposeMatrixWithZip : Num t =>
                         Vect m (Vect n t) ->
                         Vect n (Vect m t)
transposeMatrixWithZip [] = createEmptyVector
transposeMatrixWithZip (x :: xs) = let xsTrans = transposeMatrixWithZip xs in
                                   zipWith (::) x xsTrans

addVector : Num t =>
            Vect n t ->
            Vect n t ->
            Vect n t
addVector = zipWith (+)
-- or:
-- addVector xs = zipWith (+) xs
-- or:
-- addVector [] [] = []
-- addVector (x :: xs) (y :: ys) = x + y :: addVector xs ys

multVector : Num t =>
             Vect n t ->
             Vect n t ->
             t
multVector xs ys = sum $ zipWith (*) xs ys
-- or:
-- multVector xs ys = foldl (+) 0 $ zipWith (*) xs ys
-- or:
-- multVector [] [] = 0
-- multVector (x :: xs) (y :: ys) = (x * y) + multVector xs ys

addMatrix : Num t =>
           Vect m (Vect n t) ->
           Vect m (Vect n t) ->
           Vect m (Vect n t)
addMatrix = zipWith (addVector)
-- or:
-- addMatrix [] [] = []
-- addMatrix (x :: xs) (y :: ys) = addVector x y :: addMatrix xs ys

multMatrixHelper2 : Num t =>
                    Vect n t ->
                    Vect p (Vect n t) ->
                    Vect p t
multMatrixHelper2 x ys = map (multVector x) ys
-- or:
-- multMatrixHelper2 _ [] = []
-- multMatrixHelper2 x (y :: ys) = multVector x y :: multMatrixHelper2 x ys

multMatrixHelper : Num t =>
                   Vect m (Vect n t) ->
                   Vect p (Vect n t) ->
                   Vect m (Vect p t)
multMatrixHelper xs ys = map (flip multMatrixHelper2 $ ys) xs
-- or:
-- multMatrixHelper xs ys = map (\x => multMatrixHelper2 x ys) xs
-- or:
-- multMatrixHelper [] _ = []
-- multMatrixHelper (x :: xs) ys = multMatrixHelper2 x ys :: multMatrixHelper xs ys

multMatrix : Num t =>
            Vect m (Vect n t) ->
            Vect n (Vect p t) ->
            Vect m (Vect p t)
multMatrix xs ys = multMatrixHelper xs $ transposeMatrixWithZip ys
-- or:
-- multMatrix xs ys = let ysTrans = transposeMatrixWithZip ys in
--                    multMatrixHelper xs ysTrans

v1 : Vect 3 (Vect 2 Nat)
v1 = [[1,2],[3,4],[5,6]]

v2 : Vect 2 (Vect 4 Nat)
v2 = [[7,8,9,10],[11,12,13,14]]
