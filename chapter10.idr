-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 10
-- note: some solutions may be using features not presented in chapters 1-10.

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

-- check that all functions are total
%default total

--
-- section 10.1 (examples)
--

-- first a function using a view, without `with`
-- we have:
-- - a view V : Tin -> Type
-- - a covering function covV : (x : Tin) -> V x
-- - a helper fHelp : (x : Tin) -> (form : V x) -> Tout
-- - the function f : Tin -> Tout, with f in = fHelp in (covV in)

||| A view
data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

||| The covering function of the ListLast view
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

||| The helper of the function, defined in terms of the view
describeHelperInt : (input : List Int) -> (form : ListLast input) -> String
describeHelperInt [] Empty = "Empty"
describeHelperInt (xs ++ [x]) (NonEmpty xs x)
  = "Non-empty, initial portion = " ++ show xs

||| generalized version of the helper (from Int to a)
describeHelper : Show a => (input : List a) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x)
  = "Non-empty, initial portion = " ++ show xs

||| The function using the view
describeListEndInt : List Int -> String
describeListEndInt xs = describeHelperInt xs (listLast xs)

||| generalized version of the helper (from Int to a)
describeListEnd : Show a => List a -> String
describeListEnd xs = describeHelper xs (listLast xs)

-- ok:
-- *chapter10> describeListEndInt [1,2,3]
-- "Non-empty, initial portion = [1, 2]" : String
-- *chapter10> describeListEndInt [1]
-- "Non-empty, initial portion = []" : String
-- *chapter10> describeListEndInt []
-- "Empty" : String
-- *chapter10> describeListEnd [1,2,3]
-- "Non-empty, initial portion = [1, 2]" : String
-- *chapter10> describeListEnd [1]
-- "Non-empty, initial portion = []" : String
-- *chapter10> describeListEnd $ the (List Int) []
-- "Empty" : String
-- if a is not known:
-- *chapter10> describeListEnd []
-- Can't find implementation for Show a

-- a version with `with`
-- we have:
-- - a view V : Tin -> Type
-- - a covering function covV : (x : Tin) -> V x
-- - the function f : Tin -> Tout, using the "with covV" construct

describeListEnd2 : List Int -> String
describeListEnd2 xs with (listLast xs)
  describeListEnd2 [] | Empty = "Empty"
  describeListEnd2 (ys ++ [x]) | (NonEmpty ys x)
    = "Non-empty, initial portion = " ++ show ys

partial
myReversePartial : List Int -> List Int
myReversePartial xs with (listLast xs)
  myReversePartial [] | Empty = []
  myReversePartial (ys ++ [x]) | (NonEmpty ys x) = x :: myReversePartial ys

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ pairs)

splitList : (input : List a) -> SplitList input
splitList input = splitListHelper input input
  where
    splitListHelper : List a -> (input : List a) -> SplitList input
    splitListHelper _ [] = SplitNil
    splitListHelper _ [x] = SplitOne
    splitListHelper (_ :: _ :: counter) (item :: items)
      = case splitListHelper counter items of
         SplitNil => SplitOne
         SplitOne {x} => SplitPair [item] [x]
         SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelper _ items = SplitPair [] items

partial
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ pairs) | (SplitPair lefts rights)
    = merge (mergeSort lefts) (mergeSort rights)

--
-- section 10.1 (exercises)
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
-- section 10.2 (examples)
--

data SnocList0 ty = SnocEmpty0 | Snoc0 (SnocList0 ty) ty

reverseSnoc0 : SnocList0 ty -> List ty
reverseSnoc0 SnocEmpty0 = []
reverseSnoc0 (Snoc0 xs x) = x :: reverseSnoc0 xs

data MySnocList : List a -> Type where
  MySnocEmpty : MySnocList []
  MySnoc : (rec : MySnocList xs) -> MySnocList (xs ++ [x])

snocListHelp : (snoc : MySnocList input) -> (rest : List a) ->
               MySnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) = rewrite appendAssociative input [x] xs in
                                        (snocListHelp (MySnoc snoc {x}) xs)

mySnocList : (xs : List a) -> MySnocList xs
mySnocList xs = snocListHelp MySnocEmpty xs

myReverseHelper : (input : List a) -> MySnocList input -> List a
myReverseHelper [] MySnocEmpty = []
myReverseHelper (xs ++ [x]) (MySnoc rec) = myReverseHelper xs rec

myReverse : List a -> List a
myReverse input with (mySnocList input)
  myReverse [] | MySnocEmpty = []
  myReverse (xs ++ [x]) | (MySnoc rec) = x :: myReverse xs | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (mySnocList input1)
  isSuffix [] input2 | MySnocEmpty = True
  isSuffix (xs ++ [x]) input2 | (MySnoc xsrec) with (mySnocList input2)
    isSuffix (xs ++ [x]) [] | (MySnoc xsrec) | MySnocEmpty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (MySnoc xsrec) | (MySnoc ysrec)
      = if x == y then isSuffix xs ys | xsrec | ysrec
                  else False

mergeSort2 : Ord a => List a -> List a
mergeSort2 input with (splitRec input)
  mergeSort2 [] | SplitRecNil = []
  mergeSort2 [x] | SplitRecOne = [x]
  mergeSort2 (lefts ++ rights) | (SplitRecPair lrec rrec)
    = merge (mergeSort lefts | lrec)
            (mergeSort rights | rrec)

--
-- section 10.2 (exercises)
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
-- for exercises relative to the DataStore, see DataStore10.idr and TestStore10.idr
-- for exercises relative to Shapes, see Shapes10.idr and TestShapes10.idr
--
