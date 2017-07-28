

import System

import data.Vect

readToBlank: IO (List String)
readToBlank = do input <- getLine
                 if length input == 0
                    then pure List.Nil
                    else map (\tail => input :: tail) readToBlank

readAndSave: IO ()
readAndSave = do contentToSave <- readToBlank
                 putStrLn "Enter a filname: "
                 filename <- getLine
                 let content = concat (intersperse "\n" contentToSave)
                 result <- writeFile filename content 
                 case result of
                      Left _ => putStrLn "error while writing the file"
                      Right _ => putStrLn "Successfully saved file"

getLineOfFile : File -> IO (Either FileError String)
getLineOfFile = fGetLine

contentOfFile : (file: File) -> IO (n ** Vect n String)
contentOfFile file = do isEnd <- fEOF file
                        nextLine <- fGetLine file
                        case (isEnd, nextLine) of
                             (True, _) => pure (_ ** [])
                             (_, Left _) => pure (_ ** [])
                             (_, Right line) => do (_ ** rest) <- contentOfFile file
                                                   pure (_ ** line :: rest)

readVectFile : (filename: String) -> IO (n ** Vect n String)
readVectFile filename = do Right fileHandle <- openFile filename Read
                             | Left err => pure (_ ** [])
                           content <- contentOfFile fileHandle
                           closeFile fileHandle
                           pure content

                    
