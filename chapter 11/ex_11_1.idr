
import Data.Primitives.Views

every_other : Stream a -> Stream a
every_other (_ :: (x :: xs)) = x :: every_other xs

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList  xs, ys, zs

Functor InfList where
  map f (x :: xs) = f x :: map f xs

data Face : Type where
   Head : Face
   Tail : Face

total
getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem == 0 then Head
                                                        else Tail

total
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z s = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs
                            
                            
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in 
                   (seed' `shiftR` 2) :: randoms seed'

next_approx : (approx : Double) -> (num : Double) -> Double
next_approx approx num = (approx + (num / approx)) / 2

square_root_approx : (num : Double) -> (approx : Double) -> Stream Double
square_root_approx num approx = let next = (approx + (num / approx)) / 2 in
                                    approx :: square_root_approx approx next

square_root_bound : (max : Nat) -> (num : Double) -> (bound : Double) -> (approx : Stream Double) -> Double
square_root_bound Z num bound (value :: xs) = value
square_root_bound (S k) num bound (value :: xs) = if value * value - num < bound 
                                                     then value
                                                     else square_root_bound k num bound ((next_approx value num) :: value :: xs)


square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001 (square_root_approx number number)
