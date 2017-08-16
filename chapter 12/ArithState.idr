
import Data.Primitives.Views
import System

%default total


data Fuel = Dry | More (Lazy Fuel)

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

initState : GameState
initState = MkGameState (MkScore 0 0) 12

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff = record { difficulty = newDiff } 

addWrong : GameState -> GameState
addWrong = record { score -> attempted $= S }

addCorrect : GameState -> GameState
addCorrect = record { score->attempted $= S
                    , score->correct $= S }

data Command : Type -> Type where
  PutStrLn : String -> Command ()
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Bind : Command a -> (a -> Command b) -> Command b
  Pure : ty -> Command ty

Functor Command where
  map func x = Bind x (Pure . func)

Applicative Command where
  pure = Pure
  (<*>) f a = Bind f (\f' =>
              Bind a (\a' =>
              Pure (f' a')))
Monad Command where
  (>>=) = Bind



runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand rnds state (PutStrLn x) = do putStrLn x
                                        pure ((), rnds, state)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)
runCommand (r :: rs) state GetRandom 
   = pure (getRandom r (difficulty state), rs, state)
     where 
       getRandom : Int -> Int -> Int
       getRandom val max with (divides val max)
         getRandom val 0 | DivByZero = 1
         getRandom ((max * div) + rem) max | (DivBy) prf = abs rem + 1
runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState x) = pure ((), rnds, x)
runCommand rnds state (Bind x f) = do (res, rs, newState) <- runCommand rnds state x
                                      runCommand rs newState (f res)
runCommand rnds state (Pure x) = pure (x, rnds, state)

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'
arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
where
  bound : Int -> Int
  bound num with (divides num 12)
    bound ((12 * div) + rem) | (DivBy prf) = rem + 1


partial
forever : Fuel
forever = More forever

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer (cast answer))

run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run Dry stream state cmd = pure (Nothing, stream, state)
run (More fuel) stream state (Quit y) = pure (Just y, stream, state)
run (More fuel) stream state (Do z f) = do (res, newStream, newState) <- runCommand stream state z
                                           run fuel newStream newState (f res)


mutual
  correct : ConsoleIO GameState
  correct = do state <- GetGameState
               PutStrLn "Correct!"
               PutGameState (addCorrect state)
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong x = do state <- GetGameState
               PutStrLn ("Wrong, the answer was " ++ show x)
               PutGameState (addWrong state)
               quiz

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStrLn (show st)
            Answer answer <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
              | QuitCmd => Quit st
            if answer == num1 * num2 
               then correct
               else wrong (num1 * num2)

partial 
main : IO ()
main = do seed <- time
          (Just score, _, state) <- run forever (randoms (fromInteger seed)) initState quiz
            | _ => putStrLn "No fuel left"
          putStrLn ("Final score: " ++ show score)
