
import Data.Vect

MaryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
MaryInVector = There (There Here)

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value (value :: ys) {prf = Here} = ys
removeElem_auto value {n = Z}(y :: []) {prf = (There later)} = absurd later
removeElem_auto value {n = (S k)}(y :: ys) {prf = (There later)} = y :: removeElem_auto value ys
