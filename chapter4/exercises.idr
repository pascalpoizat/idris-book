-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 4

import Data.Vect

-- check that all functions are total
%default total

--
-- section 4.1
-- see BSTree.idr
-- see Expr.idr
-- see Shape.idr
--

--
-- section 4.2
-- see Vehicle.idr
--

-- first version, does not output the same error than in the book
-- > vectTake1 3 [1,2,3,4,5,6,7]
-- [1, 2, 3] : Vect 3 Integer
-- > vectTake1 8 [1,2,3,4,5,6,7]
-- (input):1:11:When checking argument prf to function Data.Fin.fromInteger:
--         When using 8 as a literal for a Fin 8
--                 8 is not strictly less than 8
vectTake1 : (q : Fin (S n)) -> Vect n t -> Vect (finToNat q) t
vectTake1 FZ _ = []
vectTake1 (FS x) [] impossible
vectTake1 (FS x) (y :: ys) = y :: vectTake1 x ys

-- second version
-- > vectTake2 3 [1,2,3,4,5,6,7]
-- [1, 2, 3] : Vect 3 Integer
-- > vectTake2 8 [1,2,3,4,5,6,7]
-- (input):1:14:When checking argument xs to constructor Data.Vect.:::
--         Type mismatch between
--                 Vect 0 elem (Type of [])
--         and
--                 Vect (S k) t (Expected type)
--
--         Specifically:
--                 Type mismatch between
--                         0
--                 and
--                         S k
vectTake2 : (q : Nat) -> Vect (q+k) t -> Vect q t
vectTake2 Z _ = []
vectTake2 (S k) (x :: xs) = x :: vectTake2 k xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                (Just x) => Just (index x xs + index x ys)

--
-- section 4.3
-- see DataStore.idr
--
