{-# LANGUAGE RankNTypes,
             TypeOperators #-}
module Parsley.Core.Primitives (module Parsley.Core.Primitives) where

import Parsley.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..))
import Parsley.Core.Defunc        (Defunc)
import Parsley.Common.Indexed     (Fix(In), (:+:)(..))

-- Parser wrapper type
newtype Parser a = Parser {unParser :: Fix (Combinator :+: ScopeRegister) a}

-- Core smart constructors
{-# INLINE _pure #-}
_pure :: Defunc a -> Parser a
_pure = Parser . In . L . Pure

infixl 4 <*>
(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (In (L (p :<*>: q)))

infixl 4 <*
(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (In (L (p :<*: q)))

infixl 4 *>
(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (In (L (p :*>: q)))

empty :: Parser a
empty = Parser (In (L Empty))

infixl 3 <|>
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (In (L (p :<|>: q)))

{-# INLINE _satisfy #-}
_satisfy :: Defunc (Char -> Bool) -> Parser Char
_satisfy = Parser . In . L . Satisfy

lookAhead :: Parser a -> Parser a
lookAhead = Parser . In . L . LookAhead . unParser

notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . In . L . NotFollowedBy . unParser

try :: Parser a -> Parser a
try = Parser . In . L . Try . unParser

{-# INLINE _conditional #-}
_conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))

branch :: Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (In (L (Branch c p q)))

chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre (Parser op) (Parser p) = Parser (In (L (ChainPre op p)))

chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost (Parser p) (Parser op) = Parser (In (L (ChainPost p op)))

newRegister :: Parser a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister (Parser p) f = Parser (In (R (ScopeRegister p (unParser . f))))

get :: Reg r a -> Parser a
get (Reg reg) = Parser (In (L (GetRegister reg)))

put :: Reg r a -> Parser a -> Parser ()
put (Reg reg) (Parser p) = Parser (In (L (PutRegister reg p)))

debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (In (L (Debug name p)))