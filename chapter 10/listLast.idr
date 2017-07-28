import Data.List.Views

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])


listLast : (ls : List a) -> (ListLast ls)
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd : Show a => List a -> String
describeListEnd xs with (listLast xs)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "Non-empty, initial: " ++ show ys

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitCons : (left : List a) -> (right : List a) -> SplitList (left ++ right)

total
splitList : (ls : List a) -> SplitList ls
splitList ls = splitListHelper ls ls 
  where
    splitListHelper : List a -> (input : List a) -> SplitList input
    splitListHelper _ [] = SplitNil
    splitListHelper _ [x] = ?types
    splitListHelper (_ :: _ :: counter) (item :: items)
      = case splitListHelper counter items of
             SplitNil => SplitOne
             SplitOne {x} => SplitCons [item] [x]
             SplitCons lefts rights => SplitCons (item :: lefts) rights
    splitListHelper _ items = SplitCons [] items


-- mergeSort : Ord a => List a -> List a
-- mergeSort input with (splitRec input)
--   mergeSort [] | SplitRecNil = []
--   mergeSort [x] | SplitRecOne = [x]
--   mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

mergeSort : Ord a =>  List a -> List a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec) = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)
