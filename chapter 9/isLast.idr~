
data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [3,2,3] 3
last123 = LastCons (LastCons LastOne)

emptyCantLast: Last [] value -> Void
emptyCantLast LastOne impossible
emptyCantLast (LastCons _) impossible

NotLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
NotLast contra LastOne = contra Refl
NotLast contra (LastCons prf) = emptyCantLast prf

rest : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
rest contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No emptyCantLast
isLast (x :: []) value = case decEq x value of
                              Yes Refl => Yes LastOne
                              No contra => No (NotLast contra)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of
                                     Yes prf => Yes (LastCons prf)
                                     No contra => No (rest contra)
