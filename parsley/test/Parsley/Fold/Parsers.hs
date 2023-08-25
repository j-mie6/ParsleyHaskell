{-# LANGUAGE CPP, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Parsley.Fold.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Parsley
import Parsley.Fold
import Parsley.Defunctionalized

#define QQ(x) (makeQ (x) [|| x ||])

plusOne :: Parser Int
plusOne = prefix (string "++" $> QQ(succ)) (char '1' $> LIFTED 1)

plusOne' :: Parser Int
plusOne' = -- line needed to avoid CPP problems (without cpphs)
  prefix (try (string "++") $> QQ(succ)) (char '1' $> LIFTED 1)

plusOnePure :: Parser Int
plusOnePure = try (prefix (string "++" $> QQ(succ)) (pure (LIFTED 1))) <|> pure (LIFTED 0)

onePlus :: Parser Int
onePlus = postfix (char '1' $> LIFTED 1) (string "++" $> QQ(succ))

onePlus' :: Parser Int
onePlus' = -- line needed to avoid CPP problems (without cpphs)
  postfix (char '1' $> LIFTED 1) (try (string "++") $> QQ(succ))

manyAA :: Parser [String]
manyAA = many (string "aa")

someA :: Parser String
someA = some (char 'a')

many2A :: Parser String
many2A = manyN 2 (char 'a')
