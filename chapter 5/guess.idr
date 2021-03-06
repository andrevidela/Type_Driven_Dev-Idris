module Main

import System

readNumber : IO (Maybe Nat)
readNumber = do input <- getLine
                if all isDigit (unpack input)
                   then pure (Just (cast input))
                   else pure Nothing


guess: (target: Nat) -> (count: Nat) -> IO ()
guess target count = do putStrLn "Enter a guess "
                        Just num <- readNumber | Nothing => do putStrLn "not a number"
                                                               guess count target
                        case compare num target of
                             GT => putStrLn "Your guess is too big " >>= \_ => guess target (S count) 
                             EQ => putStrLn $ "You guessed correctly after " ++ (show count) ++ " attempts"
                             Lt => putStrLn "Your guess is too small" >>= \_ => guess target (S count)

random : IO (Integer)
random = do rand <- time
            pure (mod rand 100)

main : IO ()
main = do randomInt <- random
          guess (fromIntegerNat randomInt) 0


countdown : (secs: Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S time) = do printLn (S time)
                        usleep 1000000
                        countdown time


countdowns : IO ()
countdowns = do putStrLn "Enter a Starting Number: "
                Just startNum <- readNumber | Nothing => do putStrLn "invalid input"
                                                            countdowns
                countdown startNum
                putStrLn "another one?"
                answer <- getLine
                if answer == "y"
                   then countdowns
                   else putStrLn "bye"
                 

myReplWith : (state: a) -> (prompt: String) -> (onInput : a -> String -> Maybe (String, a)) -> IO ()
myReplWith state prompt onInput = do putStrLn prompt
                                     inputStr <- getLine
                                     case onInput state inputStr of
                                          Just (outputStr, newState) => do putStrLn outputStr
                                                                           myReplWith newState prompt onInput
                                          Nothing => pure ()

myRepl : (prompt : String) -> (onInput : String -> String) -> IO ()
myRepl prompt onInput = myReplWith () prompt $ \_, input => Just ((onInput input), ())

