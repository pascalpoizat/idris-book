-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 9
-- note: some solutions may be using features not presented in chapters 1-9.

import Data.Vect

-- check that all functions are total
%default total

--
-- section 9.1 (examples)
--

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later)
  = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} ->
                  Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf


removeElem' : (value : a) -> (xs : Vect (S n) a) ->
              {auto prf : Elem value xs} ->
              Vect n a
removeElem' value (value :: ys) {prf = Here} = ys
removeElem' {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem' {n = (S k)} value (y :: ys) {prf = There later}
  = y :: removeElem' value ys

--
-- section 9.1 (exercices)
--

data Elem' : a -> List a -> Type where
  Here : Elem' x (x :: xs)
  There : Elem' x xs -> Elem' x (y :: xs)

-- *chapter9> the (Elem' 2 [1, 2, 4]) (There Here)
-- There Here : Elem' 2 [1, 2, 4]
-- *chapter9> the (Elem' 7 [1, 2, 4]) (There Here)
-- (input):1:26-35:When checking an application of constructor Main.There:
--         Type mismatch between
--                 Elem' 2 [2, 4] (Type of Here)
--         and
--                 Elem' 7 [2, 4] (Expected type)
--
--         Specifically:
--                 Type mismatch between
--                         2
--                 and
--                         7

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

-- *chapter9> the (Last [1,2,3] 3) $ LastCons (LastCons LastOne)
-- LastCons (LastCons LastOne) : Last [1, 2, 3] 3

noLastInEmpty : Last [] value -> Void
noLastInEmpty LastOne impossible
noLastInEmpty (LastCons _) impossible

noLastInLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
noLastInLast contra LastOne = contra Refl
noLastInLast _ (LastCons LastOne) impossible
noLastInLast _ (LastCons (LastCons _)) impossible

noLastRec : (contra : Last (x :: xs) value -> Void) ->
            Last (y :: (x :: xs)) value -> Void
noLastRec contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No noLastInEmpty
isLast [x] value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No contra) => No (noLastInLast contra)
isLast (y :: x :: xs) value = case isLast (x :: xs) value of
                              (Yes prf) => Yes (LastCons prf)
                              (No contra) => No (noLastRec contra)
