
data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z [] = Exact []
takeN (S k) [] = Fewer
takeN Z (x :: xs) = Exact []
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupBy : (n : Nat) -> List a -> List (List a)
groupBy n xs with (takeN n xs)
  groupBy size list | Fewer = [list]
  groupBy size (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupBy size rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves value | Fewer = (value, [])
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
