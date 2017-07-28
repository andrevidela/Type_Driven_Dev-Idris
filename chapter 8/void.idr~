
data MyVect : (len : Nat) -> (elem : Type) -> Type where
  Nil : MyVect 0 a
  Cons : (elem : a) -> (xs : MyVect n a) -> MyVect (S n) a

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSucc : (x : Nat) -> S x = x -> Void
valueNotSucc _ Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

succNotZero : (S k = 0) -> Void
succNotZero Refl impossible

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSucc
checkEqNat (S k) Z = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                           No contra => No (noRec contra)
                           Yes prf => Yes (cong prf)

headUnequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} -> 
                         (contra : (x = y) -> Void) ->  ((Cons x xs) = (Cons y ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : MyVect n a} -> {ys : MyVect n a} ->
                         (contra : (xs = ys) -> Void) -> ((Cons x xs) = (Cons y ys)) -> Void
tailUnequal contra Refl = contra Refl


consEqual : (headPrf : x = y) -> (tailPrf : xs = ys) -> Cons x xs = Cons y ys
consEqual Refl Refl = Refl

DecEq a => DecEq (MyVect n a) where
  decEq [] [] = Yes Refl
  decEq (Cons x xs) (Cons y ys) = case (decEq x y, decEq xs ys) of
                                       (Yes headPrf, Yes tailPrf) => Yes (consEqual headPrf tailPrf)
                                       (No headContra, _) => No $ headUnequal headContra
                                       (_, No tailContra) => let contra = tailUnequal tailContra in
                                                                 No contra

