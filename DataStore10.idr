-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 10, DataStore
-- this is only for the DataStore in chapter 10, for other chapters see the chapterXX.idr files

module DataStore10

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) ->
             DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) ->
                StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (val :: xs) = SAdd (storeViewHelp xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items
