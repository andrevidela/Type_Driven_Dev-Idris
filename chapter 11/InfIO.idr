import Data.Primitives.Views
import System

%default total

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run Dry (Do action cont) = putStrLn "No fuel left" 
run (More fuel) (Do action cont) = do res <- action
                                      run fuel (cont res)

(>>=) : IO a -> (a -> Inf InfIO ) -> InfIO
(>>=) = Do

loopPrint : String -> InfIO
loopPrint msg = do putStrLn msg
                   loopPrint msg

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'
arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
where
  bound : Int -> Int
  bound num with (divides num 12)
    bound ((12 * div) + rem) | (DivBy prf) = rem + 1


quiz : Stream Int -> (score : Nat) -> InfIO
quiz (num1 :: num2 :: nums) score = do putStrLn ("Score so far: " ++ show score)
                                       putStr (show num1 ++ " * " ++ show num2 ++ "?")
                                       answer <- getLine
                                       if cast answer == num1 * num2
                                          then do putStrLn "Correct!"
                                                  quiz nums (score + 1)
                                          else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                                                  quiz nums score

partial
main : IO ()
main = do seed <- time
          run forever $ quiz (arithInputs (fromInteger seed)) 0

total
totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do putStrLn $ action prompt
                             line <- getLine
                             totalREPL line action

greet : InfIO 
greet = do putStr "Enter your name: "
           name <- getLine
           putStrLn ("Hello " ++ name)
           greet

