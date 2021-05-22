module NandlangBench.Parsley.Functions where

import Data.Char (isAlpha, isAlphaNum)
import Data.Set (fromList, member)

nandIdentStart :: Char -> Bool
nandIdentStart c = isAlpha c || c == '_'

nandIdentLetter :: Char -> Bool
nandIdentLetter c = isAlphaNum c || c == '_'

nandUnreservedName :: String -> Bool
nandUnreservedName = \s -> not (member s keys)
  where
    keys = fromList ["if", "else", "while",
                     "function", "var"]

nandStringLetter :: Char -> Bool
nandStringLetter c = (c /= '"') && (c /= '\\') && (c > '\026')