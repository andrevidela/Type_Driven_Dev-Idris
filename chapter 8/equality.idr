import Data.Vect
    
checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = map cong $ checkEqNat k j


exactLength : (len : Nat) -> Vect n a -> Maybe (Vect len a)
exactLength {n} len xs = do Refl <- checkEqNat len n
                            Just xs

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists prf prf1 = case prf of
                           Refl => cong prf1

data ThreeEq : a -> b -> c -> Type where
  Same : ThreeEq a a a 

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x Same = Same
