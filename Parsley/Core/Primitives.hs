module Parsley.Core.Primitives (
    Parser,
    Reg,
    module Parsley.Core.Primitives
  ) where

import Prelude hiding             (pure)
import Parsley.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), Parser(..))
import Parsley.Core.Defunc        (Defunc(BLACK))
import Parsley.Common.Indexed     (Fix(In), (:+:)(..))
import Parsley.Common.Utils       (WQ)

class ParserOps rep where
  pure :: rep a -> Parser t a
  satisfy :: rep (Char -> Bool) -> Parser Char Char
  conditional :: [(rep (a -> Bool), Parser t b)] -> Parser t a -> Parser t b -> Parser t b

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
_pure :: Defunc a -> Parser t a
_pure = Parser . In . L . Pure

infixl 4 <*>
(<*>) :: Parser t (a -> b) -> Parser t a -> Parser t b
Parser p <*> Parser q = Parser (In (L (p :<*>: q)))

infixl 4 <*
(<*) :: Parser t a -> Parser t b -> Parser t a
Parser p <* Parser q = Parser (In (L (p :<*: q)))

infixl 4 *>
(*>) :: Parser t a -> Parser t b -> Parser t b
Parser p *> Parser q = Parser (In (L (p :*>: q)))

empty :: Parser t a
empty = Parser (In (L Empty))

infixr 3 <|>
(<|>) :: Parser t a -> Parser t a -> Parser t a
Parser p <|> Parser q = Parser (In (L (p :<|>: q)))

{-# INLINE _satisfy #-}
_satisfy :: Defunc (Char -> Bool) -> Parser Char Char
_satisfy = Parser . In . L . Satisfy

lookAhead :: Parser t a -> Parser t a
lookAhead = Parser . In . L . LookAhead . unParser

notFollowedBy :: Parser t a -> Parser t ()
notFollowedBy = Parser . In . L . NotFollowedBy . unParser

try :: Parser t a -> Parser t a
try = Parser . In . L . Try . unParser

{-# INLINE _conditional #-}
_conditional :: [(Defunc (a -> Bool), Parser t b)] -> Parser t a -> Parser t b -> Parser t b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))

branch :: Parser t (Either a b) -> Parser t (a -> c) -> Parser t (b -> c) -> Parser t c
branch (Parser c) (Parser p) (Parser q) = Parser (In (L (Branch c p q)))

chainPre :: Parser t (a -> a) -> Parser t a -> Parser t a
chainPre (Parser op) (Parser p) = Parser (In (L (ChainPre op p)))

chainPost :: Parser t a -> Parser t (a -> a) -> Parser t a
chainPost (Parser p) (Parser op) = Parser (In (L (ChainPost p op)))

newRegister :: Parser t a -> (forall r. Reg r a -> Parser t b) -> Parser t b
newRegister (Parser p) f = Parser (In (R (ScopeRegister p (unParser . f))))

get :: Reg r a -> Parser t a
get (Reg reg) = Parser (In (L (GetRegister reg)))

put :: Reg r a -> Parser t a -> Parser t ()
put (Reg reg) (Parser p) = Parser (In (L (PutRegister reg p)))

debug :: String -> Parser t a -> Parser t a
debug name (Parser p) = Parser (In (L (Debug name p)))