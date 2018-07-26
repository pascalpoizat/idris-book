-- exercices in "Type-Driven Development with Idris" Edit
-- chapter 6
-- note: some solutions may be using features not presented in chapters 1-6.
-- wrt the exercice on the use of 'do', we sometimes rather use:
-- f x >>= Just . X
-- instead of:
-- do v <- f x
--    Just (X v)

import Data.Vect

-- check that all functions are total
%default total

--
-- section 6.1 (examples)
--

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety-four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x

--
-- section 6.2 (examples)
--

||| defines types of functions with n arguments of kind t -> t -> ... -> t
AdderType : (n : Nat) -> Type -> Type
AdderType Z t = t
AdderType (S k) t = (next : t) -> AdderType k t

-- *chapter6> :let A2 = AdderType 2
-- *chapter6> :let A4 = AdderType 4
-- *chapter6> A2 Nat
-- Nat -> Nat -> Nat : Type
-- *chapter6> A4 Int
-- Int -> Int -> Int -> Int -> Int : Type

||| generic adder of type t -> (t -> t -> ... -> t)
||| where the first argument is the accumulator
adder : Num t => (n : Nat) -> (acc : t) -> AdderType n t
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

||| adder for 3 naturals
add3Nat : AdderType 3 Nat
add3Nat = adder 3 0

val1 : Nat
val1 = add3Nat 1 2 3

val2 : Int
val2 = (adder 4 0) 1 2 3 4

-- *chapter6> val1
-- 6 : Nat
-- *chapter6> val2
-- 10 : Int

--
-- section 6.2 (exercices)
--

Matrix : (rows : Nat) -> (cols : Nat) -> Type -> Type
Matrix n m t = Vect n (Vect m t)

testMatrix : Matrix 2 3 Double
testMatrix = [[0,0,0],[0,0,0]]

-- we rewrite the examples from Chapter 3

createEmptyVector : Matrix n 0 t
createEmptyVector {n} = replicate n []

transposeMatrix : Matrix m n t -> Matrix n m t
transposeMatrix [] = createEmptyVector
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                                zipWith (::) x xsTrans

addVector : Num t => Vect n t -> Vect n t -> Vect n t
addVector = zipWith (+)

multVector : Num t => Vect n t -> Vect n t -> t
multVector xs ys = sum $ zipWith (*) xs ys

addMatrix : Num t => Matrix m n t -> Matrix m n t -> Matrix m n t
addMatrix = zipWith (addVector)

multMatrixHelper2 : Num t => Vect n t -> Matrix p n t -> Vect p t
multMatrixHelper2 x ys = map (multVector x) ys

multMatrixHelper : Num t => Matrix m n t -> Matrix p n t -> Matrix m p t
multMatrixHelper xs ys = map (flip multMatrixHelper2 $ ys) xs

multMatrix : Num t => Matrix m n t -> Matrix n p t -> Matrix m p t
multMatrix xs ys = multMatrixHelper xs $ transposeMatrix ys

v1 : Matrix 3 2 Nat
v1 = [[1,2],[3,4],[5,6]]

v2 : Matrix 2 4 Nat
v2 = [[7,8,9,10],[11,12,13,14]]

v1v1 : Matrix 3 2 Nat
v1v1 = addMatrix v1 v1
-- v1v1 : Matrix 3 2 Nat
-- [[2, 4], [6, 8], [10, 12]] : Vect 3 (Vect 2 Nat)

v1v2 : Matrix 3 4 Nat
v1v2 = multMatrix v1 v2
-- v1v2 : Matrix 3 4 Nat
-- [[29, 32, 35, 38], [65, 72, 79, 86], [101, 112, 123, 134]] : Vect 3 (Vect 4 Nat)

-- we get nice error messages
--
-- *chapter6> addMatrix v1 v2
-- (input):1:1-15:When checking an application of function Main.addMatrix:
--         Type mismatch between
--                 Matrix 2 4 Nat (Type of v2)
--         and
--                 Matrix 3 2 Nat (Expected type)
-- *chapter6> multMatrix v1 v1
-- (input):1:1-16:When checking an application of function Main.multMatrix:
--         Type mismatch between
--                 Matrix 3 2 Nat (Type of v1)
--         and
--                 Matrix 2 p Nat (Expected type)

data Format = Number Format
            | Doubble Format
            | Str Format
            | Chhar Format
            | Lit String Format
            | End
%name Format fmt, fmt1, fmt2, fmt3

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Doubble fmt) = (d : Double) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Chhar fmt) = (car : Char) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printFmt (Number fmt) acc = \i => printFmt fmt (acc ++ show i)
printFmt (Doubble fmt) acc = \d => printFmt fmt (acc ++ show d)
printFmt (Str fmt) acc = \str => printFmt fmt (acc ++ str)
printFmt (Chhar fmt) acc = \char => printFmt fmt (acc ++ show char)
printFmt (Lit str fmt) acc = printFmt fmt (acc ++ str)
printFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Doubble (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chhar (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                          Lit str chars' => Lit (strCons c str) chars'
                          fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printFmt _ ""
-- *chapter6> :t printf "%s = %d"
-- printf "%s = %d" : String -> Int -> String
-- *chapter6> :t printf "%c %f"
-- printf "%c %f" : Char -> Double -> String

val3 : String
val3 = printf "%s = %d" "val2" val2
-- "val2 = 10" : String
-- *chapter6> printf "%c %f" 'X' 24
-- "'X' 24.0" : String

TupleVect : (n : Nat) -> Type -> Type
TupleVect Z t = ()
TupleVect (S k) t = (t, TupleVect k t)

test : TupleVect 4 Nat
test = (1,2,3,4,())

--
-- section 6.3
--

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
