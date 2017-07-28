

printLonger: IO ()
printLonger = do putStrLn "enter a first line:"
                 firstLine <- getLine
                 putStrLn "enter a second line:"
                 secondLine <- getLine
                 let maxLength = max (length firstLine) (length secondLine)
                 putStrLn $ show  maxLength

printLongerBind: IO ()
printLongerBind = putStrLn "Enter a first line: " >>= \_ =>
                  getLine >>= \firstLine =>
                  putStrLn "enter a secondLine: " >>= \_ =>
                  getLine >>= \secondLine => 
                  let maxLength = max (length firstLine) (length secondLine) in
                      putStrLn $ show maxLength


