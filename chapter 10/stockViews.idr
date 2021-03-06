import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

-- returns maximum equal suffix of two inputs:
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (xs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) = if y == x 
         then (equalSuffix xs ys | xsrec | ysrec) ++ [x]
         else []

mergeSort : Ord a => Vect n a -> Vect n a 
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) = merge (mergeSort ys | lrec) (mergeSort zs | rrec)


toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = "0" ++ (toBinary n | rec)
  toBinary (S (n + n)) | (HalfRecOdd rec) = "1" ++ (toBinary n | rec)

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = if x == y 
                                                   then palindrome ys | rec
                                                   else False
