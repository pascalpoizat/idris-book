-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 4

import Data.Vect

-- check that all functions are total
%default total

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
