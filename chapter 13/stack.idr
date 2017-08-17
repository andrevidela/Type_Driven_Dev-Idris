
import Data.Vect

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S h) (S h)

  GetStr : StackCmd String h h
  PutStr : String -> StackCmd () h h

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a h1 h2 -> (a -> StackCmd b h2 h3) -> StackCmd b h1 h3

data StackIO : Nat -> Type where
  Do : StackCmd a h1 h2 ->
       (a -> Inf (StackIO h2)) -> 
       StackIO h1

namespace StackDo
  (>>=) : StackCmd a h1 h2 ->
          (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial 
forever : Fuel
forever = More forever


testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)



runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)

runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr str) = do putStr str
                               pure ((), stk)

runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= f) = do (res, newStk) <- runStack stk cmd
                              runStack newStk (f res)

run : Fuel -> Vect h Integer -> StackIO h -> IO ()
run Dry stk (Do x f) = pure ()
run (More fuel) stk (Do x f) = do (res, newStk) <- runStack stk x
                                  run fuel newStk (f res)


data StkInput = Add | Number Integer

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput num = if all isDigit (unpack num)
                    then Just (Number (cast num))
                    else Nothing

mutual 
  tryAdd : StackIO height
  tryAdd {height = (S (S k))}= do doAdd
                                  result <- Top
                                  PutStr (show result ++ "\n")
                                  stackCalc
  tryAdd = do PutStr "less than two items on the stack, can't add \n"
              stackCalc

  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid Input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just (Add) => tryAdd
                      
partial
main : IO ()
main = do run forever [] stackCalc
