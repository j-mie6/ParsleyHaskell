{-|
Module      : Parsley.Register
Description : The register combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module exposes combinators designed to work with /registers/. These are small pieces of state
that are carried through the parsing process. They can be used, for example, to perform indentation
sensitive parsing. In fact, they are a flexible replacement for the monadic combinators, in conjunction
with the "Parsley.Selective" combinators. In particular, the `bind` combinator implements a limited form
of the @(>>=)@ operation, where the structure of the resulting parser will still be statically
determinable. Registers paired with "Parsley.Selective" combinators are Turing-Compete.

@since 0.1.0.0
-}
module Parsley.Register (
    module Parsley.Register,
    module Primitives
  ) where

import Prelude hiding        (pure, (<*>), (*>), (<*))
import Parsley.Alternative   (empty, (<|>))
import Parsley.Applicative   (pure, (<*>), (*>), (<*))
import Parsley.Internal.Core (Parser, ParserOps)
import Parsley.Selective     (when, while)

import Parsley.Internal.Core.Primitives as Primitives (Reg, newRegister, get, put)

newRegister_ :: ParserOps rep => rep a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister_ x = newRegister (pure x)

put_ :: ParserOps rep => Reg r a -> rep a -> Parser ()
put_ r = put r . pure

gets :: Reg r a -> Parser (a -> b) -> Parser b
gets r p = p <*> get r

gets_ :: ParserOps rep => Reg r a -> rep (a -> b) -> Parser b
gets_ r = gets r . pure

modify :: Reg r a -> Parser (a -> a) -> Parser ()
modify r p = put r (gets r p)

modify_ :: ParserOps rep => Reg r a -> rep (a -> a) -> Parser ()
modify_ r = modify r . pure

move :: Reg r1 a -> Reg r2 a -> Parser ()
move dst src = put dst (get src)

bind :: Parser a -> (Parser a -> Parser b) -> Parser b
bind p f = newRegister p (f . get)

local :: Reg r a -> Parser a -> Parser b -> Parser b
local r p q = bind (get r) $ \x -> put r p
                                *> q
                                <* put r x

swap :: Reg r1 a -> Reg r2 a -> Parser ()
swap r1 r2 = bind (get r1) $ \x -> move r1 r2
                                *> put r2 x

rollback :: Reg r a -> Parser b -> Parser b
rollback r p = bind (get r) $ \x -> p <|> put r x *> empty

for :: Parser a -> Parser (a -> Bool) -> Parser (a -> a) -> Parser () -> Parser ()
for init cond step body =
  newRegister init $ \i ->
    let cond' :: Parser Bool
        cond' = gets i cond
    in when cond' (while (body *> modify i step *> cond'))