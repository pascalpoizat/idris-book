-- exercices in "Type-Driven Development with Idris" Edit
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
biggestTriangle (Combine pic1 pic2) = maxMaybe (biggestTriangle pic1) (biggestTriangle pic2)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3)) (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3)) (Primitive (Circle 4))
