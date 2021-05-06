module Parsley.Fold.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Parsley
import Parsley.Fold
import Parsley.Garnish

plusOne :: Parser Int
plusOne = chainPre (string "++" $> code succ) (char '1' $> code 1)

plusOne' :: Parser Int
plusOne' = chainPre (try (string "++") $> code succ) (char '1' $> code 1)

plusOnePure :: Parser Int
plusOnePure = try (chainPre (string "++" $> code succ) (pure (code 1))) <|> pure (code 0)

onePlus :: Parser Int
onePlus = chainPost (char '1' $> code 1) (string "++" $> code succ)

onePlus' :: Parser Int
onePlus' = chainPost (char '1' $> code 1) (try (string "++") $> code succ)

manyAA :: Parser [String]
manyAA = many (string "aa")

someA :: Parser String
someA = some (char 'a')

many2A :: Parser String
many2A = manyN 2 (char 'a')