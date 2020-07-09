module Parsley.Core.Primitives (module Parsley.Core.Primitives) where

import Parsley.Core.CombinatorAST (Combinator(..))
import Parsley.Core.Defunc        (Defunc)
import Parsley.Common.Indexed     (Fix(In))

-- Parser wrapper type
newtype Parser a = Parser {unParser :: Fix Combinator a}

-- Core smart constructors
{-# INLINE _pure #-}
_pure :: Defunc a -> Parser a
_pure = Parser . In . Pure

infixl 4 <*>
(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (In (p :<*>: q))

infixl 4 <*
(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (In (p :<*: q))

infixl 4 *>
(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (In (p :*>: q))

empty :: Parser a
empty = Parser (In Empty)

infixl 3 <|>
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (In (p :<|>: q))

{-# INLINE _satisfy #-}
_satisfy :: Defunc (Char -> Bool) -> Parser Char
_satisfy = Parser . In . Satisfy

lookAhead :: Parser a -> Parser a
lookAhead = Parser . In . LookAhead . unParser

notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . In . NotFollowedBy . unParser

try :: Parser a -> Parser a
try = Parser . In . Try . unParser

{-# INLINE _conditional #-}
_conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (Match p fs (map unParser qs) def))

branch :: Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (In (Branch c p q))

chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre (Parser op) (Parser p) = Parser (In (ChainPre op p))

chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost (Parser p) (Parser op) = Parser (In (ChainPost p op))

debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (In (Debug name p))