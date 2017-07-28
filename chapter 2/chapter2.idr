module Main

rawpalindrome : String -> Bool
rawpalindrome x = (reverse x) == x

limitPalindrome : Nat -> String -> Bool
limitPalindrome k x = if length x > k then rawpalindrome x else False

palindrome : String -> Bool
palindrome = limitPalindrome 10

countWords : String -> Nat
countWords x = let w = words x in
                   length w

count : String -> (Nat, Nat)
count x = let words = countWords x
              length = length x in
              (words, length)

top_ten :  Ord a => List a -> List a
top_ten xs = List.take 10 $ reverse . sort $ xs

over_length : Nat -> List String -> Nat
over_length k = List.length . List.filter (\x => x > k) . map (\word => length word)

show_palindrome : String -> String
show_palindrome x = if rawpalindrome x then x ++ " is a palindrome\n"
                                       else x ++ " is not a palindrome\n"


main : IO ()
main = repl "Enter a String: "
       show_palindrome
