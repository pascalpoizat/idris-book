-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 6

import Data.Vect

-- check that all functions are total
%default total

--
-- section 6.1
--

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety-four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x

--
-- section 6.2
--

||| defines types of functions with n arguments of kind t -> t -> ... -> t
AdderType : (n : Nat) -> Type -> Type
AdderType Z t = t
AdderType (S k) t = (next : t) -> AdderType k t

-- > :let A2 = AdderType 2
-- > :let A4 = AdderType 4
-- > A2 Nat
-- Nat -> Nat -> Nat : Type
-- > A4 Int
-- Int -> Int -> Int -> Int -> Int : Type

||| generic adder of type t -> (t -> t -> ... -> t)
||| where the first argument is the accumulator
adder : Num t => (n : Nat) -> (acc : t) -> AdderType n t
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

||| adder for 3 naturals
add3Nat : AdderType 3 Nat
add3Nat = adder 3 0

val1 : Nat
val1 = add3Nat 1 2 3

val2 : Int
val2 = (adder 4 0) 1 2 3 4

-- > val1
-- 6 : Nat
-- > val2
-- 10 : Int

--
-- section 6.3
-- see DataStore.idr
--
