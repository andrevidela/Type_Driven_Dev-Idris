
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


data StkInput = Add | Number Integer | Sub | Neg | Discard | Dup

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "sub" = Just Sub
strToInput "neg" = Just Neg
strToInput "dup" = Just Dup
strToInput "discard" = Just Discard
strToInput num = if all isDigit (unpack num)
                    then Just (Number (cast num))
                    else Nothing

mutual 

  tryBinaryOp : (Integer -> Integer -> Integer) -> StackIO h
  tryBinaryOp op { h = (S (S k))}= do i1 <- Pop
                                      i2 <- Pop
                                      Push (op i2 i1)
                                      result <- Top
                                      PutStr (show result ++ "\n")
                                      stackCalc
  tryBinaryOp op = do PutStr ("not enough elements on stack")
                      stackCalc

  tryUnaryOp : (Integer -> Integer) -> StackIO h
  tryUnaryOp op {h = (S k)} = do val <- Pop
                                 Push (op val)
                                 result <- Top
                                 PutStr (show result ++ "\n")
                                 stackCalc
  tryUnaryOp op = do PutStr ("not enough elements on stack")
                     stackCalc

  tryDup : StackIO h
  tryDup {h = (S k)}= do val <- Top
                         Push val
                         PutStr ("duplicated " ++ show val ++ "\n")
                         stackCalc
  tryDup = do PutStr ("not enough elements on stack")
              stackCalc

  stackCalc : StackIO h
  stackCalc {h}= do  PutStr "> "
                     input <- GetStr
                     case strToInput input of
                          Nothing => do PutStr "Invalid Input\n"
                                        stackCalc
                          Just (Number x) => do Push x
                                                stackCalc
                          Just (Add) => tryBinaryOp (+)
                          Just (Sub) => tryBinaryOp (-)
                          Just (Neg) => tryUnaryOp (* (-1))
                          Just (Discard) => tryBinaryOp (\f, s => f)
                          Just (Dup) => tryDup
                      
partial
main : IO ()
main = do run forever [] stackCalc
