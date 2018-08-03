-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 7

-- check that all functions are total
%default total

--
-- Binary Search Trees
--

data BST elem = Empty
              | Node (BST elem) elem (BST elem)

-- from Haskell's Data.Tree
shift : String -> String -> List String -> List String
shift str1 str2 strings
  = zipWith (++) (take (length strings) $ str1 :: repeat str2) strings

-- from Haskell's Data.Tree
partial
draw : Show elem => BST elem -> List String
draw Empty = ["*"]
draw (Node left x right) = (show x) :: helper [left, right]
where
  partial
  helper : List (BST elem) -> List String
  helper [] = []
  helper (t :: []) = "|" :: shift "`- " "   " (draw t)
  helper (t :: ts) = "|" :: shift "+- " "|  " (draw t) ++ helper ts

-- from Haskell's Data.Tree
partial
drawTree : Show elem => BST elem -> String
drawTree = unlines . draw

partial
Show elem => Show (BST elem) where
  show x = drawTree x

insert : Ord elem => elem -> BST elem -> BST elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right)
 = case compare x val of
     LT => Node (insert x left) val right
     EQ => orig
     GT => Node left val (insert x right)

listToTree : Ord a => List a -> BST a
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

treeToList : BST a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right

Functor BST where
  map func Empty = Empty
  map func (Node left val right) =
    Node (map func left) (func val) (map func right)

-- we have two alternatives to implement Foldable for BST
-- one here: following https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html
-- one in chapter 7 of the book
--
-- > :let tree = listToTree [1,4,6,7,3]
-- > foldr (::) [] tree
-- [1, 3, 4, 6, 7] : List Integer
-- > foldl (\x,y => x ++ [y]) [] tree
-- [1, 3, 4, 6, 7] : List Integer
--
-- > foldr @{chapter} (::) [] tree
-- [3, 7, 6, 4, 1] : List Integer
-- > foldl @{chapter} (\x,y => x ++ [y]) [] tree
-- [3, 7, 6, 4, 1] : List Integer

-- following https://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html
-- foldr func (func e (foldr func acc right)) left
--
Foldable BST where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let rightVal = foldr func acc right
        eVal = func e rightVal
    in
        foldr func eVal left

-- following the chapter
-- func e (foldr func (foldr func acc left) right)
--
[chapter] Foldable BST where
  foldr func acc Empty = acc
  foldr func acc (Node left e right) =
    let leftVal = foldr func acc left
        rightVal = foldr func leftVal right
    in
        func e rightVal

-- call with:
-- > :exec printTree $ listToTree [1,4,6,3,7]
-- 7
-- |
-- +- 3
-- |  |
-- |  +- 1
-- |  |  |
-- |  |  +- *
-- |  |  |
-- |  |  `- *
-- |  |
-- |  `- 6
-- |     |
-- |     +- 4
-- |     |  |
-- |     |  +- *
-- |     |  |
-- |     |  `- *
-- |     |
-- |     `- *
-- |
-- `- *
partial
printTree : Show elem => (BST elem) -> IO ()
printTree t = do putStrLn (show t)
