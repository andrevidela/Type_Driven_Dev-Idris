
module Main

import Data.Vect

tryIndex : Integer -> Vect size a -> Maybe a
tryIndex {size} i xs = case integerToFin i size of
                         Nothing => Nothing
                         (Just idx) => Just (index idx xs)

data PowerSource = Petrol | Pedal | Electricity

data Vehicle : PowerSource -> Type where
     Bicycle : Vehicle Pedal
     Car : (fuel: Nat) -> Vehicle Petrol
     Bus : (fuel: Nat) -> Vehicle Petrol
     Unicyle: Vehicle Pedal
     MotorCycle: (fuel: Nat) -> Vehicle Petrol
     ElectricCar: (charge: Nat) -> Vehicle Electricity
     Tram: (charge: Nat) -> Vehicle Electricity


wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicyle = 1
wheels (MotorCycle fuel) = 2
wheels (ElectricCar charge) = 4
wheels (Tram charge) = 8


refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 100
refuel (MotorCycle fuel) = MotorCycle 100


takeVect : (m : Nat) -> Vect (m + n) a -> Vect m a
takeVect Z xs = []
takeVect (S x) (y :: xs) = y :: takeVect x xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos [] [] = Nothing
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                (Just x) => Just ((index x xs) + (index x ys))

