module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SChar
            | SInt
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

addToStore : (dataStore : DataStore) -> SchemaType (schema dataStore) -> DataStore
addToStore (MkData schema size items) newItem = MkData schema _ (items ++ [newItem])

sumInput : Integer -> String -> Maybe (String, Integer)
sumInput sum inp = let newVal = cast inp in
                       if newVal < 0
                          then Nothing
                          else let newTotal = sum + newVal in
                                   Just ("SubTotal " ++ show newTotal ++ "\n", newTotal)

data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  GetAll : Command schema
  Quit : Command schema

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: []) = Just SString
parseSchema ("String" :: xs) = map ((.+.) SString) (parseSchema xs)
parseSchema ("Int" :: []) = Just SInt
parseSchema ("Int" :: xs) = map ((.+.) SInt) (parseSchema xs)
parseSchema ("Char" :: []) = Just SChar
parseSchema ("Char" :: xs) = map ((.+.) SChar) (parseSchema xs)
parseSchema _ = Nothing


parsePrefix : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema, String)
parsePrefix SChar str = case unpack str of
                             c :: ' ' :: rest => Just (c, ltrim $ pack rest)
                             _ => Nothing
parsePrefix SInt str = case span isDigit str of
                            ("", _) => Nothing
                            (digits, rest) => Just (cast digits, ltrim rest)
parsePrefix (schemal .+. schemar) str = do 
                                        (l_val, input') <- parsePrefix schemal str
                                        (r_val, input'') <- parsePrefix schemar input'
                                        Just ((l_val, r_val), input'')
parsePrefix SString str = getQuoted (unpack str)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: rest) = case List.span (/= '"') rest of
                                   (quoted, '"' :: tail) => Just (pack quoted, ltrim $ pack tail)
                                   _ => Nothing
    getQuoted _ = Nothing

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
                                (Just (parsed, "")) => Just (parsed)
                                Nothing => Nothing
                                (Just _) => Nothing

parseCommand : (schema: Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "get" "" = Just (GetAll)
parseCommand schema "get" index = if all isDigit (unpack index)
                                     then Just (Get (cast index))
                                     else Nothing
parseCommand schema "add" str = map (Add) (parseBySchema schema str)
parseCommand schema "quit" "" = Just (Quit)
parseCommand schema "schema" rest = map (SetSchema) (parseSchema (words rest))
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case Strings.span (/= ' ') input of
                   (cmd, args) => parseCommand schema cmd (ltrim args)


display : SchemaType schema-> String
display {schema = SString} x = x
display {schema = SInt} x = show x
display {schema = (y .+. z)} (a, b) = display a ++ ", " ++ display b

getEntry : (idx : Integer) -> (dataStore : DataStore) -> Maybe (String, DataStore)
getEntry idx dataStore = case integerToFin idx (size dataStore) of
                                Nothing => Just ("Out of range\n", dataStore)
                                (Just x) => Just (display (index x (items dataStore)) ++ "\n", dataStore)

listFindings : String -> Vect n String -> List (Nat, String)
listFindings query vect = let is = Data.Vect.findIndices (Strings.isInfixOf query) vect in
                              map (\i => (finToNat i, index i vect)) is


-- displayRestuls : (dataStore : DataStore) -> (results : List (Nat, (SchemaStore dataStore)) -> String
-- displayRestuls results = unlines $ ( map (\pair => show (fst pair) ++ ": " ++ show (snd pair))) $ results
-- 
-- searchEntries : (query : String) -> (dataStore : DataStore) ->  Maybe (String, DataStore)
-- searchEntries query dataStore = case listFindings query (items dataStore) of
--                                      [] => Just ("No result", dataStore)
--                                      results => Just (displayRestuls results, dataStore)
-- 

setSchema : (store: DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              (S _) => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput dataStore input = case parse (schema dataStore) input of
                                    Nothing => Just ("Invalid Command\n", dataStore)
                                    (Just (SetSchema schema')) => case setSchema dataStore schema' of
                                                                       Nothing => Just ("Can't update schema\n", dataStore)
                                                                       Just store' => Just ("OK\n", store')
                                    (Just (Add item)) => Just ("ID " ++ show (size dataStore) ++ "\n", addToStore dataStore item)
                                    (Just (Get x)) => getEntry x dataStore
                                    (Just (GetAll)) => let entries = map display (items dataStore) in
                                                           Just (unlines $ toList entries, dataStore)
                                    (Just Quit) => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
