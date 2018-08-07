-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 12

module Tree

-- check that all functions are total
%default total

public export
data Tree a = Empty
            | Node (Tree a) a (Tree a)

-- from Haskell's Data.Tree
private
shift : String -> String -> List String -> List String
shift str1 str2 strings
  = zipWith (++) (take (length strings) $ str1 :: repeat str2) strings

-- from Haskell's Data.Tree
partial private
draw : Show a => Tree a -> List String
draw Empty = ["*"]
draw (Node left x right) = (show x) :: helper [left, right]
where
  partial
  helper : List (Tree a) -> List String
  helper [] = []
  helper (t :: []) = "|" :: shift "`- " "   " (draw t)
  helper (t :: ts) = "|" :: shift "+- " "|  " (draw t) ++ helper ts

-- from Haskell's Data.Tree
partial private
drawTree : Show a => Tree a -> String
drawTree = unlines . draw

partial export
Show a => Show (Tree a) where
  show x = drawTree x

export
flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right
