import Data.Vect

myAppend_rhs_2 : Vect (S (m + len)) a -> Vect (plus m (S len)) a
myAppend_rhs_2 {m} {len} xs = rewrite sym (plusSuccRightSucc m len) in xs

myAppend : Vect n a -> Vect m a -> Vect (m + n) a
myAppend {m} [] ys = rewrite plusZeroRightNeutral m in ys
myAppend (x :: xs) ys = myAppend_rhs_2 (x :: myAppend xs ys)
