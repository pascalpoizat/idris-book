-- examples in "Type-Driven Development with Idris"
-- chapter 15, section 15.2

import ProcessLib

-- check that all functions are total
%default total

-- service inputs
data ListAction : Type where
  Length : List elem -> ListAction
  Append : List elem -> List elem -> ListAction

-- outputs wrt. inputs
ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {elem} xs ys) = List elem

-- service
procList : Service ListType ()
procList = do Respond (\msg => case msg of
                                (Length xs) => Pure $ length xs
                                (Append xs ys) => Pure $ xs ++ ys)
              Loop procList

-- client
procMain : Client ()
procMain = do Just list <- Spawn procList
              | Nothing => Action (putStrLn "Spawn failed")
              len <- Request list (Length [1,2,3])
              Action (printLn len)
              app <- Request list (Append [1,2,3] [4,5,6])
              Action (printLn app)

-- run with:
-- :exec runProc procMain
