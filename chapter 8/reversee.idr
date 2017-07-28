
import Data.Vect

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

reverseProof : Vect (len + 1) a -> Vect (S len) a
reverseProof {len} ys = rewrite plusCommutative 1 len in ys

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = reverseProof $ myReverse xs ++ [x]

proof_cons : Vect ((S n1) + len) a -> Vect (plus n1 (S len)) a
proof_cons {n1} {len} xs = rewrite sym $  plusSuccRightSucc n1 len in xs


proof_nil : Vect n1 a -> Vect (plus n1 0) a
proof_nil {n1} xs = rewrite plusZeroRightNeutral n1 in xs

exReverse : Vect n a -> Vect n a
exReverse xs = reverse' [] xs
               where 
                 reverse' : (acc: Vect n a) -> Vect m a -> Vect (n + m) a
                 reverse' acc [] = proof_nil acc
                 reverse' acc (x :: xs) = proof_cons $ reverse' (x :: acc) xs
