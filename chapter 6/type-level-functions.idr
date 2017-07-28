StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int


getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "some string"
getStringOrInt True = 18

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x


AdderType : Num n => (numargs : Nat) -> Type -> Type
AdderType Z n = n
AdderType (S k) n = (next : n) -> AdderType k n

adder : Num n => (numargs : Nat) -> (acc: n) -> AdderType numargs n
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)
