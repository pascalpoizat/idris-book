-- exercises in "Type-Driven Development with Idris"
-- chapter 10

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

-- check that all functions are total
%default total

--
-- section 10.1
--

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ xs)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

-- more explicit using `with`
takeN' : (n : Nat) -> (xs : List a) -> TakeN xs
takeN' Z xs = Exact []
takeN' (S k) [] = Fewer
takeN' (S k) (x :: xs) with (takeN' k xs)
  takeN' (S k) (x :: xs) | Fewer = Fewer
  takeN' (S k) (x :: (n_xs ++ ys)) | (Exact n_xs) = Exact (x :: n_xs)

partial
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

partial
groupByN' : (n : Nat) -> (xs : List a) -> List (List a)
groupByN' n xs with (takeN' n xs)
  groupByN' n xs | Fewer = [xs]
  groupByN' n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN' n rest

partial
halves : List a -> (List a, List a)
halves xs with (takeN (length xs `div` 2) xs)
  halves xs | Fewer = (xs, [])
  halves (n_xs ++ ys) | (Exact n_xs) = (n_xs, ys)

--
-- section 10.2
--

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec)
      = if x == y then (equalSuffix xs ys | xsrec | ysrec) ++ [x]
                  else []

mergeSortVect : Ord a => Vect n a -> Vect n a
mergeSortVect xs with (splitRec xs)
  mergeSortVect [] | SplitRecNil = []
  mergeSortVect [x] | SplitRecOne = [x]
  mergeSortVect (lefts ++ rights) | (SplitRecPair lrec rrec)
    = merge (mergeSortVect lefts | lrec)
            (mergeSortVect rights | rrec)

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

-- needed due to lazy argument of HalfRec
-- use :exec toBinaryMain $ toBinary 42
toBinaryMain : Nat -> IO ()
toBinaryMain k = do putStrLn $ toBinary k

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec)
    = (x == y) && palindrome ys | rec

--
-- section 10.3 (exercises)
-- see DataStore.idr and TestStore.idr
-- see Shape.idr and TestShape.idr
--
