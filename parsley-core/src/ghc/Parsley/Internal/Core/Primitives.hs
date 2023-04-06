{-# LANGUAGE PatternSynonyms #-}
module Parsley.Internal.Core.Primitives (
    Parser,
    Reg,
    module Parsley.Internal.Core.Primitives
  ) where

import Prelude hiding                      (pure, (<*>))
import Parsley.Internal.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), Parser(..), PosSelector(..), pattern Empty, pattern FailErr, pattern UnexpectedErr)
import Parsley.Internal.Core.Defunc        (Defunc, charPred)

import Parsley.Internal.Common.Indexed     (Fix(In), (:+:)(..))

-- Core smart constructors
{-# INLINE pure #-}
pure :: Defunc a -> Parser a
pure = Parser . In . L . Pure

{-# INLINE satisfy #-}
satisfy :: Defunc (Char -> Bool) -> Parser Char
satisfy = Parser . In . L . Satisfy . charPred

{-# INLINE conditional #-}
conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))

{-# INLINE (<*>) #-}
(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (In (L (p :<*>: q)))

{-# INLINE (<*) #-}
(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (In (L (p :<*: q)))

{-# INLINE (*>) #-}
(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (In (L (p :*>: q)))

{-# INLINE empty #-}
empty :: Parser a
empty = Parser (In (L Empty))

{-# INLINE (<|>) #-}
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (In (L (p :<|>: q)))

{-# INLINE lookAhead #-}
lookAhead :: Parser a -> Parser a
lookAhead = Parser . In . L . LookAhead . unParser

{-# INLINE notFollowedBy #-}
notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . In . L . NotFollowedBy . unParser

{-# INLINE try #-}
try :: Parser a -> Parser a
try = Parser . In . L . Try . unParser

{-# INLINE branch #-}
branch :: Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (In (L (Branch c p q)))

{-# INLINE loop #-}
loop :: Parser () -> Parser a -> Parser a
loop (Parser body) (Parser exit) = Parser (In (L (Loop body exit)))

{-# INLINE newRegister #-}
newRegister :: Parser a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister (Parser p) f = Parser (In (R (ScopeRegister p (unParser . f))))

{-# INLINE get #-}
get :: Reg r a -> Parser a
get (Reg reg) = Parser (In (L (GetRegister reg)))

{-# INLINE put #-}
put :: Reg r a -> Parser a -> Parser ()
put (Reg reg) (Parser p) = Parser (In (L (PutRegister reg p)))

{-# INLINE line #-}
line :: Parser Int
line = Parser (In (L (Position Line)))

{-# INLINE col #-}
col :: Parser Int
col = Parser (In (L (Position Col)))

{-# INLINE debug #-}
debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (In (L (Debug name p)))

{-# INLINE label #-}
label :: String -> Parser a -> Parser a
label name (Parser p) = Parser (In (L (LabelErr name p)))

{-# INLINE explain #-}
explain :: String -> Parser a -> Parser a
explain reason (Parser p) =  Parser (In (L (ExplainErr reason p)))

{-# INLINE fail #-}
fail :: [String] -> Parser a
fail msgs =  Parser (In (L (FailErr msgs)))

{-# INLINE unexpected #-}
unexpected :: String -> Parser a
unexpected token =  Parser (In (L (UnexpectedErr token)))

{-# INLINE amend #-}
amend :: Parser a -> Parser a
amend (Parser p) =  Parser (In (L (AmendErr p)))

{-# INLINE entrench #-}
entrench :: Parser a -> Parser a
entrench (Parser p) =  Parser (In (L (EntrenchErr p)))
