module CommonFunctions where

isDigit :: Char -> Bool
isDigit c
    |    c == '0' || c == '1' || c == '2' || c == '3'
    || c == '4' || c == '5' || c == '6' || c == '7'
    || c == '8' || c == '9' = True
    | otherwise = False

toDigit :: Char -> Int
toDigit c = fromEnum c - fromEnum '0'