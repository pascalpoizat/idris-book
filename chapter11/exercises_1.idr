-- exercises in "Type-Driven Development with Idris"
-- chapter 11, section 1

import Data.Primitives.Views

-- check that all functions are total
%default total

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

every_other : Stream Int -> Stream Int
every_other (first :: second :: rest) = second :: every_other rest

Functor InfList where
  map f (value :: xs) = f value :: map f xs

countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

data Face = Head | Tails

partial
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips n xs = map helper $ take n xs
  where
    total
    helper : Int -> Face
    helper x with (divides x 2)
      helper ((2 * div) + rem) | (DivBy prf)
        = if rem == 0 then Head else Tails

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                (seed' `shiftR` 2) :: randoms seed'

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
  = approx :: (square_root_approx number next)
    where
      next = (approx + (number / approx)) / 2

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z _ _ (val :: _) = val
square_root_bound (S k) n bound (val :: xs)
  = if (abs (val * val - n)) <= bound
      then val
      else square_root_bound k n bound xs

square_root : (number : Double) -> Double
square_root n = square_root_bound 100 n 0.00000000001 (square_root_approx n n)
