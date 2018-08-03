-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 6

-- check that all functions are total
%default total

--
-- section 6.2
-- see Matrix.idr
-- see Printf.idr
--

TupleVect : (n : Nat) -> Type -> Type
TupleVect Z t = ()
TupleVect (S k) t = (t, TupleVect k t)

test : TupleVect 4 Nat
test = (1,2,3,4,())

--
-- section 6.3
-- see DataStore.idr
--
