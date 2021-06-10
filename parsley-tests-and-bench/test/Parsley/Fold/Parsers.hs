{-# LANGUAGE TemplateHaskell #-}
module Parsley.Fold.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Parsley
import Parsley.Fold
import Parsley.Garnish

plusOne :: Parser Int
plusOne = chainPre (string "++" $> [|succ|]) (char '1' $> [|1|])

plusOne' :: Parser Int
plusOne' = chainPre (try (string "++") $> [|succ|]) (char '1' $> [|1|])

plusOnePure :: Parser Int
plusOnePure = try (chainPre (string "++" $> [|succ|]) (pure ([|1|]))) <|> pure ([|0|])

onePlus :: Parser Int
onePlus = chainPost (char '1' $> [|1|]) (string "++" $> [|succ|])

onePlus' :: Parser Int
onePlus' = chainPost (char '1' $> [|1|]) (try (string "++") $> [|succ|])

manyAA :: Parser [String]
manyAA = many (string "aa")

someA :: Parser String
someA = some (char 'a')

many2A :: Parser String
many2A = manyN 2 (char 'a')