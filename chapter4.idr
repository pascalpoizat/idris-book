-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 4
-- note: some solutions are using features not presented in chapters 1-4.

import Data.Vect

-- check that all functions are total
%default total

--
-- Shapes and pictures
--

||| Represents shapes
data Shape = ||| A triangle, with its base length and height
             Triangle Double Double
           | ||| A rectangle, with its length and height
             Rectangle Double Double
           | ||| A circle with its radius
             Circle Double
%name Shape shape, shape1, shape2

||| Area of a shape
area : Shape -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

||| Represents pictures
data Picture = ||| A primitive shape
               Primitive Shape
             | ||| The combination of two pictures
               Combine Picture Picture
             | ||| The rotation of a picture, given the angle and the picture
               Rotate Double Picture
             | ||| The translation of a picture, given dx, dy, and the picture
               Translate Double Double Picture
%name Picture pic, pic1, pic2

rectangle : Picture
rectangle = Primitive $ Rectangle 20 10

circle : Picture
circle = Primitive $ Circle 5

triangle : Picture
triangle = Primitive $ Triangle 10 10

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                               (Translate 15 25 triangle))

||| Area of a picture
pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate x pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic

--
-- Trees
--

||| A binary search tree.
data BST : Type -> Type where
  ||| An empty tree.
  Empty : Ord elem =>
          BST elem
  ||| A node with a value, a left subtree, and a right subtree.
  ||| Elements in the left subtree must be strictly lower than the value.
  ||| Elements in the right subtree must be strictly greater than the value.
  Node : Ord elem =>
         (left : BST elem) ->
         (val : elem) ->
         (right : BST elem) ->
         BST elem

||| insert a value in a binary search tree
insert : elem -> BST elem -> BST elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
  = case compare x val of
      LT => Node (insert x left) val right
      EQ => orig
      GT => Node left val (insert x right)
--
-- section 4.1
--

listToTree : Ord a => List a -> BST a
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

treeToList : BST a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right

||| An integer arithmetic expression
data Expr = ||| A single integer
            Value Int
          | ||| Addition of an expression to an expression
            Addition Expr Expr
          | ||| Subtraction of an expression from an expression
            Subtraction Expr Expr
          | ||| Multiplication of an expression with an expression
            Multiplication Expr Expr

||| Evaluate an expression
evaluate : Expr -> Int
evaluate (Value x) = x
evaluate (Addition x y) = evaluate x + evaluate y
evaluate (Subtraction x y) = evaluate x - evaluate y
evaluate (Multiplication x y) = evaluate x * evaluate y

||| Computes the largest of two inputs or Nothing if both are Nothing
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe (Just x) Nothing = Just x
maxMaybe Nothing (Just y) = Just y
maxMaybe (Just x) (Just y) = Just (max x y)

||| Biggest triangle
biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive tri@(Triangle x y)) = Just (area tri)
biggestTriangle (Primitive (Rectangle x y)) = Nothing
biggestTriangle (Primitive (Circle x)) = Nothing
biggestTriangle (Combine pic1 pic2)
  = maxMaybe (biggestTriangle pic1) (biggestTriangle pic2)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3)) (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3)) (Primitive (Circle 4))

--
-- section 4.2
--

||| Powersources for vehicles
data PowerSource = Petrol | Pedal | Electric

||| Vehicles
data Vehicle : PowerSource -> Type where
  Unicycle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electric
  ElectricCar : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Unicycle = 1
wheels Bicycle = 2
wheels Motorcycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Tram = 10
wheels ElectricCar = 2

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motorcycle fuel) = Motorcycle 50
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel Unicycle impossible
refuel Bicycle impossible
refuel Tram impossible
refuel ElectricCar impossible

-- first version, does not output the same error than in the book
-- *chapter4> vectTake1 3 [1,2,3,4,5,6,7]
-- [1, 2, 3] : Vect 3 Integer
-- *chapter4> vectTake1 8 [1,2,3,4,5,6,7]
-- (input):1:11:When checking argument prf to function Data.Fin.fromInteger:
--         When using 8 as a literal for a Fin 8
--                 8 is not strictly less than 8
vectTake1 : (q : Fin (S n)) -> Vect n t -> Vect (finToNat q) t
vectTake1 FZ _ = []
vectTake1 (FS x) [] impossible
vectTake1 (FS x) (y :: ys) = y :: vectTake1 x ys

-- second version
-- *chapter4> vectTake2 3 [1,2,3,4,5,6,7]
-- [1, 2, 3] : Vect 3 Integer
-- *chapter4> vectTake2 8 [1,2,3,4,5,6,7]
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
-- section 4.3 (data store, see also the update of this example in chapter 6)
--

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : (store : DataStore) -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size store) newItem = MkData (S size) (addToData store)
  where
    addToData : Vect oldsize String -> Vect (S oldsize) String
    addToData [] = [newItem]
    addToData (x :: xs) = x :: addToData xs

||| Supported commands
data Command = ||| Add an item
               Add String
             | ||| Get an item by its id
               Get Integer
             | ||| Search an item
               Search String
             | ||| Get the number of items
               Size
             | |||| Quit
               Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "search" str = Just (Search str)
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store
  = let store_items = items store in
      case integerToFin pos (size store) of
        Nothing => Just ("Out of range \n", store)
        Just id => Just ((index id store_items) ++ "\n", store)

findFromSubstring : (store : DataStore) -> (str : String) -> List (Nat, String)
findFromSubstring store str = helper (items store) str 0
  where
    helper : Vect n String -> String -> Nat -> List (Nat, String)
    helper [] _ _ = []
    helper (x :: xs) s k = case isInfixOf s x of
                                False => helper xs s (S k)
                                True => (k, x) :: helper xs s (S k)

presentResults : List (Nat, String) -> String
presentResults results = foldl (++) "" $ map helper results
  where
    helper : (Nat, String) -> String
    helper (x, res) = show x ++ ": " ++ res ++ "\n"

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse input of
        Nothing => Just ("Invalid command\n", store)
        Just (Add item) =>
          Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
        Just (Get pos) => getEntry pos store
        Just (Search str) =>
          let foundItems = findFromSubstring store str in
            Just (presentResults foundItems, store)
        Just Size => Just (show (size store) ++ "\n", store)
        Just Quit => Nothing

partial
main : IO ()
main = replWith (MkData _ []) "Command: " processInput
