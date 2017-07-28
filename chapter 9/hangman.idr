import Data.Vect

cannotBeInNil : (x : a) -> (later : Elem value []) -> Vect 0 a
cannotBeInNil _ Here impossible
cannotBeInNil _ (There _) impossible

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem x (x :: xs) {prf = Here} = xs
removeElem value (x :: []) {prf = (There later)} = cannotBeInNil x later
removeElem value (x :: (y :: xs)) {prf = (There later)} = x :: (removeElem value (y :: xs))

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
  Lost : (game : WordState Z (S letters)) -> Finished
  Won : (game : WordState (S guesses) Z) -> Finished

data ValidInput : List Char -> Type where
  IsValid : (c : Char) -> ValidInput [c]

Uninhabited (ValidInput (x :: (y :: xs))) where
  uninhabited (IsValid _) impossible

Uninhabited (ValidInput []) where
  uninhabited (IsValid _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No absurd
isValidInput (x :: []) = Yes (IsValid x)
isValidInput (x :: (y :: xs)) = No absurd

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess: "
               line <- getLine
               case isValidString (toUpper line) of
                    Yes prf => pure (_ ** prf) 
                    No contra => do putStrLn "invalid guess"
                                    readGuess

processGuess : (letter : Char) -> WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = case isElem letter missing of 
                                                      Yes prf => Right (MkWordState word (removeElem letter missing))
                                                      No contra => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do (_ ** IsValid letter) <- readGuess
                                 case processGuess letter st of
                                      Left l => do putStrLn "Wrong!"
                                                   case guesses of
                                                        Z => pure (Lost l)
                                                        S k => game l
                                      Right r => do putStrLn "Right!"
                                                    case letters of
                                                         Z => pure (Won r)
                                                         S k => game r

main : IO ()
main = do result <- game {guesses=2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
               Lost (MkWordState word missing) =>
                    putStrLn ("You lose. The word was " ++ word)
               Won (MkWordState word missing) =>
                    putStrLn ("You win! The word was " ++ word)

