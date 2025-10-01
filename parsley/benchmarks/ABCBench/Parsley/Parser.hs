{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas -Wno-incomplete-patterns #-}
{-# HLINT ignore "Redundant bracket" #-}
module ABCBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)

import Parsley
import Parsley.Combinator       (eof, more)
import Parsley.Defunctionalized
import Parsley.Char             (noneOf, token)
import Parsley.Fold
import Language.Haskell.TH.Syntax (Lift(..))

import Parsley.Register
import Parsley.Defunctionalized

#define QQ(x) (makeQ (x) [||(x)||])

count :: Parser a -> Parser Int
count = manyl (FLIP_H $ APP_H CONST (QQ(succ))) (LIFTED 0)

abc :: Parser ()
abc = newRegister (count (char 'a')) $ \n ->
         downTo0 n (void $ char 'b')
      *> downTo0 n (void $ char 'c')
      *> eof
    where downTo0 n = for (get n) (pure (makeQ ((> 0)) [|| (> 0) ||])) (pure (makeQ (subtract 1) [|| subtract 1 ||]))

abcPEG :: Parser ()
abcPEG = asbscs
    where
        asbscs = lookAhead (asbs *> char 'c') *> ascs *> eof
        ascs = (char 'a' *> ascs <* char 'c') <|> skipMany (char 'b')
        asbs = optional (try (char 'a' *> asbs <* char 'b'))
