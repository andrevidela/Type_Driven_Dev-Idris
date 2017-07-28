
%default total


data Fuel = Dry | More (Lazy Fuel)


data RunIO : Type -> Type where
  Quit : a -> RunIO a
  Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

run : Fuel -> RunIO a -> IO (Maybe a)
run Dry y = pure Nothing
run (More x) (Quit y) = pure (Just y)
run (More fuel) (Do action next) = do result <- action
                                      run fuel (next result)


partial
forever : Fuel
forever = More forever

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet = do putStrLn "Enter your name: "
           name <- getLine
           if name == ""
              then do putStrLn "Bye bye!"
                      Quit ()
              else do putStrLn ("Hello " ++ name)
                      greet

partial 
main : IO ()
main = do run forever greet
          pure ()
