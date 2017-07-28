module Main

import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store: DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (items ++ [newItem])

sumInput : Integer -> String -> Maybe (String, Integer)
sumInput sum inp = let newVal = cast inp in
                       if newVal < 0
                          then Nothing
                          else let newTotal = sum + newVal in
                                   Just ("SubTotal " ++ show newTotal ++ "\n", newTotal)

data Command = Add String | Get Integer | Quit | Size | Search String

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "get" index = if all isDigit (unpack index)
                              then Just (Get (cast index))
                              else Nothing
parseCommand "add" str = Just (Add str)
parseCommand "quit" "" = Just (Quit)
parseCommand "size" "" = Just (Size)
parseCommand "search" str = Just (Search str)
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case Strings.span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)


getEntry : (idx : Integer) -> (dataStore : DataStore) -> Maybe (String, DataStore)
getEntry idx dataStore = let item = items dataStore in
                           case integerToFin idx (size dataStore) of
                                Nothing => Just ("Out of range\n", dataStore)
                                (Just x) => Just (index x item ++ "\n", dataStore)

listFindings : String -> Vect n String -> List (Nat, String)
listFindings query vect = let is = Data.Vect.findIndices (Strings.isInfixOf query) vect in
                              map (\i => (finToNat i, index i vect)) is


displayRestuls : (results : List (Nat, String)) -> String
displayRestuls results = unlines $ ( map (\pair => show (fst pair) ++ ": " ++ show (snd pair))) $ results

searchEntries : (query : String) -> (dataStore : DataStore) ->  Maybe (String, DataStore)
searchEntries query dataStore = case listFindings query (items dataStore) of
                                     [] => Just ("No result", dataStore)
                                     results => Just (displayRestuls results, dataStore)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput dataStore input = case parse input of
                                    Nothing => Just ("Invalid Command\n", dataStore)
                                    (Just (Add item)) => Just ("ID " ++ show (size dataStore) ++ "\n", addToStore dataStore item)
                                    (Just (Get x)) => getEntry x dataStore
                                    (Just Quit) => Nothing
                                    (Just Size) => Just (show (size dataStore) ++ "\n", dataStore)
                                    (Just (Search query)) => searchEntries query dataStore

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
