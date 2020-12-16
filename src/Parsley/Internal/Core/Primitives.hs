module Parsley.Internal.Core.Primitives (
    Parser,
    Reg,
    module Parsley.Internal.Core.Primitives
  ) where

import Prelude hiding                      (pure)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), Parser(..))
import Parsley.Internal.Core.Defunc        (Defunc(BLACK))
import Parsley.Internal.Common.Indexed     (Fix(In), (:+:)(..))
import Parsley.Internal.Common.Utils       (WQ)

class ParserOps rep where
  pure :: rep a -> Parser a
  satisfy :: rep (Char -> Bool) -> Parser Char
  conditional :: [(rep (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b

instance ParserOps WQ where
  pure = pure . BLACK
  satisfy = satisfy . BLACK
  conditional cs p def = conditional (map (\(f, t) -> (BLACK f, t)) cs) p def

instance {-# INCOHERENT #-} x ~ Defunc => ParserOps x where
  pure = _pure
  satisfy = _satisfy
  conditional = _conditional

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

infixr 3 <|>
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