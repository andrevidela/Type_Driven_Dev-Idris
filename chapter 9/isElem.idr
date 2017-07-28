import Data.Vect

data ElemList : a -> List a -> Type where
  Here : ElemList x (x :: xs)
  There : (later : ElemList x xs) -> ElemList x (y :: xs)
  
cant_be_in_Nil : Elem value [] -> Void
cant_be_in_Nil Here impossible
cant_be_in_Nil (There _) impossible

notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

myIsElem : DecEq ty => (value : ty) -> (ls : Vect n ty) -> Dec (Elem value ls)
myIsElem value [] = No cant_be_in_Nil
myIsElem value (x :: xs) = case decEq value x of
                                Yes Refl => Yes Here
                                No contra => case myIsElem value xs of
                                                  Yes prf => Yes (There prf)
                                                  No notThere => No (notInTail contra notThere)

