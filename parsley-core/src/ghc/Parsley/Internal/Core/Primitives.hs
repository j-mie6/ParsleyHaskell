{-# LANGUAGE PatternSynonyms, CPP #-}
module Parsley.Internal.Core.Primitives (
    Parser,
    Reg,
    module Parsley.Internal.Core.Primitives
  ) where

import Prelude hiding                      (pure, (<*>))
import Control.Arrow                       (first)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), Parser(..))
#if MIN_VERSION_parsley_core(2,0,0)
import Parsley.Internal.Core.Defunc        (Defunc)
#else
import Parsley.Internal.Core.Defunc        (Defunc(BLACK, ID, COMPOSE), pattern FLIP_H)
import Parsley.Internal.Common.Utils       (WQ)
#endif

import Parsley.Internal.Common.Indexed     (Fix(In), (:+:)(..))

#if MIN_VERSION_parsley_core(2,0,0)
-- Core smart constructors
{-# INLINE pure #-}
pure :: Defunc a -> Parser a
pure = Parser . In . L . Pure

{-# INLINE satisfy #-}
satisfy :: Defunc (Char -> Bool) -> Parser Char
satisfy = Parser . In . L . Satisfy

{-# INLINE conditional #-}
conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))
#else
class ParserOps rep where
  pure :: rep a -> Parser a
  satisfy :: rep (Char -> Bool) -> Parser Char
  conditional :: [(rep (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b

instance ParserOps WQ where
  pure = pure . BLACK
  satisfy = satisfy . BLACK
  conditional = conditional . map (first BLACK)

instance {-# INCOHERENT #-} x ~ Defunc => ParserOps x where
  pure = _pure
  satisfy = _satisfy
  conditional = _conditional

-- Core smart constructors
{-# INLINE _pure #-}
_pure :: Defunc a -> Parser a
_pure = Parser . In . L . Pure

{-# INLINE _satisfy #-}
_satisfy :: Defunc (Char -> Bool) -> Parser Char
_satisfy = Parser . In . L . Satisfy

{-# INLINE _conditional #-}
_conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))
#endif

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

#if MIN_VERSION_parsley_core(2,0,0)
#else
{-# INLINE chainPre #-}
chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre op p =
  newRegister (pure ID) (\r ->
    loop (put r (pure (FLIP_H COMPOSE) <*> op <*> get r))
         (get r))
  <*> p

{-# INLINE chainPost #-}
chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost p op =
  newRegister p $ \r ->
    loop (put r (op <*> get r))
         (get r)
#endif

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

{-# INLINE debug #-}
debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (In (L (Debug name p)))