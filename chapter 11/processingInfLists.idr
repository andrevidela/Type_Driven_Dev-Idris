
data InfList : Type -> Type where 
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name  InfList xs, ys, zs

getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z xs = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

Functor InfList where
  map f (a :: rest) = f a :: Delay (map f rest)
