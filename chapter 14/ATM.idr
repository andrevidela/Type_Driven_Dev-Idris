import Data.Vect

Pin : Type
Pin = Vect 4 Char

data ATMState = Ready | CardInserted | Session

data PinCheck = CorrectPin | IncorrectPin

data HasCard : ATMState -> Type where
  HasCI : HasCard CardInserted
  HasSession : HasCard Session

CheckState : PinCheck -> ATMState
CheckState CorrectPin = Session
CheckState IncorrectPin = CardInserted

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardInserted)
  EjectCard : {auto prf : HasCard state} -> ATMCmd () state (const Ready)
  GetPin : ATMCmd Pin CardInserted (const CardInserted)
  CheckPin : Pin -> ATMCmd PinCheck CardInserted CheckState
  GetAmount : ATMCmd Nat state (const state)
  Dispense : (amount : Nat) -> ATMCmd () Session (const Session)
  Message : String -> ATMCmd () state (const state)
  Pure : (res : ty) -> ATMCmd ty (s_fn res) s_fn
  (>>=) : ATMCmd a s1 s2_fn ->
          ((res : a) -> ATMCmd b (s2_fn res) s3_fn) ->
          ATMCmd b s1 s3_fn

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPin
         CorrectPin <- CheckPin pin 
           | IncorrectPin => do Message "Pin is incorrect"
                                EjectCard
         cash <- GetAmount
         Dispense cash
         EjectCard

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do _ <- getChar
                pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure (ch :: chs)

testPin : Vect 4 Char
testPin = ['1','2','3','4']

runATM : ATMCmd res inState outState_fn -> IO res
runATM InsertCard = do putStrLn "Please insert your card"
                       card <- getLine
                       pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPin = do putStr "Enter Pin: "
                   readVect 4
runATM (CheckPin pin) = if pin == testPin 
                           then pure CorrectPin
                           else pure IncorrectPin
runATM GetAmount = do putStrLn "How much would you like "
                      amount <- getLine
                      pure (cast amount)
runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM (f x')

