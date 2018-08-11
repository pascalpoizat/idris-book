-- examples in "Type-Driven Development with Idris"
-- chapter 9

import Data.Vect

-- check that all functions are total
%default total

--
-- section 9.1
--

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem2 : (value : a) -> (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem2 value (value :: ys) Here = ys
removeElem2 {n = Z} value (y :: []) (There later) = absurd later
removeElem2 {n = (S k)} value (y :: ys) (There later)
  = y :: removeElem2 value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} ->
                  Vect n a
removeElem_auto value xs {prf} = removeElem2 value xs prf


removeElem : (value : a) -> (xs : Vect (S n) a) ->
              {auto prf : Elem value xs} ->
              Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later}
  = y :: removeElem value ys

--
-- section 9.2
-- see Hangman.idr
--
