
module Main

import Data.Vect

myZip : Vect a e -> Vect a f -> Vect a (e, f)
myZip [] [] = []
myZip (x :: xs) (y :: ys) = (x, y) :: myZip xs ys

main : IO ()
main = putStrLn "blabla"
