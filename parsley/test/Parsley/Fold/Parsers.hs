{-# LANGUAGE TemplateHaskell #-}
module Parsley.Fold.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Parsley
import Parsley.Fold
import Parsley.Defunctionalized

plusOne :: Parser Int
plusOne = prefix (string "++" $> makeQ succ [||succ||]) (char '1' $> LIFTED 1)

plusOne' :: Parser Int
plusOne' = prefix (try (string "++") $> makeQ succ [||succ||]) (char '1' $> LIFTED 1)

plusOnePure :: Parser Int
plusOnePure = try (prefix (string "++" $> makeQ succ [||succ||]) (pure (LIFTED 1))) <|> pure (LIFTED 0)

onePlus :: Parser Int
onePlus = postfix (char '1' $> LIFTED 1) (string "++" $> makeQ succ [||succ||])

onePlus' :: Parser Int
onePlus' = postfix (char '1' $> LIFTED 1) (try (string "++") $> makeQ succ [||succ||])

manyAA :: Parser [String]
manyAA = many (string "aa")

someA :: Parser String
someA = some (char 'a')

many2A :: Parser String
many2A = manyN 2 (char 'a')
