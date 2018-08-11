-- exercises in "Type-Driven Development with Idris"
-- chapter 4

-- check that all functions are total
%default total

--
-- Binary Search Trees
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

listToTree : Ord a => List a -> BST a
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

treeToList : BST a -> List a
treeToList Empty = []
treeToList (Node left val right) = treeToList left ++ [val] ++ treeToList right
