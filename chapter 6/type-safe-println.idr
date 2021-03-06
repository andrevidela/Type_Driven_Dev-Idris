import Data.Vect

data Format = Number Format
            | Str Format
            | Chr Format
            | Dble Format
            | Lit String Format
            | End

%name Format fmt, fmt1, fmt2


Matrix : Nat -> Nat -> Type
Matrix k j = Vect k (Vect j Int)

GenericMatric : Nat -> Nat -> Type -> Type
GenericMatric n m t = Vect n (Vect m t)

testMatrix : Matrix 2 3
testMatrix = [[1,2,3],[1,2,3]]

PrintfType : Format -> Type
PrintfType (Chr fmt) = (c : Char) -> PrintfType fmt
PrintfType (Dble fmt) = (d : Double) -> PrintfType fmt
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String


printfFmt : (fmt: Format) -> (acc: String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Lit x fmt) acc = printfFmt fmt (acc ++ x)
printfFmt End acc = acc
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ cast c)
printfFmt (Dble fmt) acc = \d => printfFmt fmt (acc ++ show d)

toFormat : (chars : List Char) -> Format
toFormat Nil = End
toFormat ('%' :: 'c' :: rest) = Chr (toFormat rest)
toFormat ('%' :: 'f' :: rest) = Dble (toFormat rest)
toFormat ('%' :: 's' :: rest) = Str (toFormat rest)
toFormat ('%' :: 'd' :: rest) = Number (toFormat rest)
--toFormat ('%' :: rest) = Lit "%" $ toFormat rest
toFormat (c :: rest) = case toFormat rest of
                            Lit lit rest' => Lit (strCons c lit) rest'
                            fmt => Lit (cast c) fmt


printf : (format : String) -> PrintfType (toFormat $ unpack format)
printf format = printfFmt _ ""

TupleVect : (n: Nat) -> Type -> Type
TupleVect Z x = ()
TupleVect (S k) type = (type, TupleVect k type)

testVect : TupleVect 4 Nat
testVect = (1,2,3,4,())
