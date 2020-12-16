{-# LANGUAGE AllowAmbiguousTypes,
             MultiParamTypeClasses #-}
module Parsley.Precedence (module Parsley.Precedence) where

import Prelude hiding                ((<$>))
import Parsley.Alternative           (choice)
import Parsley.Applicative           ((<$>))
import Parsley.Fold                  (chainPre, chainPost, chainl1', chainr1')
import Parsley.Internal.Common.Utils (WQ)
import Parsley.Internal.Core         (Parser, Defunc(BLACK, ID))

precedence :: Prec a b -> Parser a -> Parser b
precedence NoLevel atom = atom
precedence (Level lvl lvls) atom = precedence lvls (level lvl atom)
  where
    level (InfixL ops wrap) atom  = chainl1' wrap atom (choice ops)
    level (InfixR ops wrap) atom  = chainr1' wrap atom (choice ops)
    level (Prefix ops wrap) atom  = chainPre (choice ops) (wrap <$> atom)
    level (Postfix ops wrap) atom = chainPost (wrap <$> atom) (choice ops)

data Level a b = InfixL  [Parser (b -> a -> b)] (Defunc (a -> b))
               | InfixR  [Parser (a -> b -> b)] (Defunc (a -> b))
               | Prefix  [Parser (b -> b)]      (Defunc (a -> b))
               | Postfix [Parser (b -> b)]      (Defunc (a -> b))

class Monolith a b c where
  infixL  :: [Parser (b -> a -> b)] -> c
  infixR  :: [Parser (a -> b -> b)] -> c
  prefix  :: [Parser (b -> b)]      -> c
  postfix :: [Parser (b -> b)]      -> c

instance x ~ a => Monolith x a (Level a a) where
  infixL  = flip InfixL ID
  infixR  = flip InfixR ID
  prefix  = flip Prefix ID
  postfix = flip Postfix ID

instance {-# INCOHERENT #-} x ~ (WQ (a -> b) -> Level a b) => Monolith a b x where
  infixL  ops = InfixL ops . BLACK
  infixR  ops = InfixR ops . BLACK
  prefix  ops = Prefix ops . BLACK
  postfix ops = Postfix ops . BLACK

data Prec a b where
  NoLevel :: Prec a a
  Level :: Level a b -> Prec b c -> Prec a c

monolith :: [Level a a] -> Prec a a
monolith = foldr Level NoLevel