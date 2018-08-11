-- exercises in "Type-Driven Development with Idris"
-- chapter 6

import Data.Vect

-- check that all functions are total
%default total

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newItem
  = MkData schema _ (addToData store)
  where
    addToData : Vect oldsize (SchemaType schema) ->
                Vect (S oldsize) (SchemaType schema)
    addToData [] = [newItem]
    addToData (x :: xs) = x :: addToData xs

||| Supported commands
data Command : Schema -> Type where
               ||| Set schema
               SetSchema : (newSchema : Schema) -> Command schema
               ||| Add an item
               Add : SchemaType schema -> Command schema
               ||| Get an item by its id
               Get : Integer -> Command schema
               ||| List the contents of the store
               List : Command schema
               ||| Get the number of items
               Size : Command schema
               |||| Quit
               Quit : Command schema

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
  case xs of
    [] => Just SString
    _ => parseSchema xs >>= Just . (SString .+.)
parseSchema ("Int" :: xs) =
  case xs of
    [] => Just SInt
    _ => parseSchema xs >>= Just . (SInt .+.)
parseSchema ("Char" :: xs) =
  case xs of
    [] => Just SChar
    _ => parseSchema xs >>= Just . (SChar .+.)
parseSchema _ = Nothing

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs)
      = case span (/= '"') xs of
          (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
          _ => Nothing
    getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of
                      ("", rest) => Nothing
                      (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input = case unpack input of
                      [] => Nothing
                      (x :: rest) => Just (x, ltrim (pack rest))
parsePrefix (schema1 .+. schema2) input =
  do (val1, rest1) <- parsePrefix schema1 input
     (val2, rest2) <- parsePrefix schema2 rest1
     Just ((val1, val2), rest2)

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input =
  do (res, rest) <- parsePrefix schema input
     if rest == "" then Just res else Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "schema" rest
  = parseSchema (words rest) >>= Just . SetSchema
parseCommand schema "add" rest
  = parseBySchema schema rest >>= Just . Add
parseCommand schema "get" "" = Just List
parseCommand schema "get" val = case all isDigit (unpack val) of
                                  False => Nothing
                                  True => Just (Get (cast val))
parseCommand schema "size" "" = Just Size
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                      (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (item1, item2)
  = display item1 ++ ", " ++ display item2

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store
  = let store_items = items store in
      case integerToFin pos (size store) of
        Nothing => Just ("Out of range \n", store)
        Just id => Just (display (index id store_items) ++ "\n", store)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                          Z => Just (MkData schema _ [])
                          S k => Nothing

presentResults : Vect _ (Nat, SchemaType schema) -> String
presentResults results = foldl (++) "" $ map helper results
  where
    helper : (Nat, SchemaType schema) -> String
    helper (x, res) = show x ++ ": " ++ (display res) ++ "\n"

listStore : (store : DataStore) -> String
listStore store = presentResults $ helper (items store) 0
  where
    helper : Vect size' (SchemaType (schema store)) ->
             Nat ->
             Vect size' (Nat, SchemaType (schema store))
    helper [] _ = []
    helper (x :: xs) k = (k, x) :: helper xs (S k)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse (schema store) input of
        Nothing => Just ("Invalid command\n", store)
        Just (SetSchema schema') =>
          case setSchema store schema' of
            Nothing => Just ("Can't update schema\n", store)
            Just store' => Just ("OK\n", store')
        Just (Add item) =>
          Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
        Just (Get pos) => getEntry pos store
        Just List => Just (listStore store, store)
        Just Size => Just (show (size store) ++ "\n", store)
        Just Quit => Nothing

partial
main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
