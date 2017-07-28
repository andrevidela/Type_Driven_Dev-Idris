
import Data.Primitives.Views
import System

%default total


data Fuel = Dry | More (Lazy Fuel)

data Command : Type -> Type where
  PutStr : String -> Command ()
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())
  GetLine : Command String
  Pure : ty -> Command ty

runCommand : Command a -> IO a
runCommand (ReadFile filePath) = readFile filePath
runCommand (WriteFile filePath content) = writeFile filePath content
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry p = pure Nothing
run fuel (Quit val) = do pure (Just val)
run (More fuel) (Do action next) = do result <- runCommand action
                                      run fuel (next result)


partial
forever : Fuel
forever = More forever

totalREPL : (prompt : String) -> (action : String -> String) -> ConsoleIO output
totalREPL prompt action = do PutStr $ action prompt
                             line <- GetLine
                             totalREPL line action

data ParsedCommand = Cat String | Copy String String | Exit

parseCommand : String -> Maybe ParsedCommand
parseCommand str = case (words str) of
                        ("exit" :: Nil) => Just Exit
                        ("cat" :: arg :: Nil) => Just $ Cat arg
                        ("copy" :: source :: dest :: Nil) => Just $ Copy source dest
                        _ => Nothing



interactiveShell : ConsoleIO String
interactiveShell = do PutStr "Shell %>"
                      line <- GetLine
                      cmd <- Pure $ parseCommand line
                      case cmd of
                        Just Exit => Quit "Session end"
                        Just (Copy source dest) => do Right content <- ReadFile source
                                                        | Left _ => do PutStr "read error\n"
                                                                       interactiveShell
                                                      Right () <- WriteFile dest content
                                                        | Left _ => do PutStr "write error\n"
                                                                       interactiveShell
                                                      PutStr "copy succeeded\n"
                                                      interactiveShell
                        Just (Cat file) => do Right content <- ReadFile file
                                                    | Left _ => do PutStr "error\n"
                                                                   interactiveShell
                                              PutStr content
                                              interactiveShell
                        Nothing => do PutStr "Unknown command\n"
                                      interactiveShell 


partial 
main : IO ()
main = do Just result <- run forever interactiveShell
          putStrLn $ show result
