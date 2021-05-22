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
    Reg, newRegister, get, put,
    newRegister_,
    put_,
    gets, gets_,
    modify, modify_,
    move, swap,
    bind, local, rollback,
    for
  ) where

import Prelude hiding      (pure, (<*>), (*>), (<*))
import Parsley.Alternative (empty, (<|>))
import Parsley.Applicative (pure, (<*>), (*>), (<*))
import Parsley.Internal    (Parser, ParserOps, Reg, newRegister, get, put)
import Parsley.Selective   (when, while)

{-|
Like `newRegister`, except the initial value of the register is seeded from a pure value as opposed
to the result of a parser.

@since 0.1.0.0
-}
newRegister_ :: ParserOps rep => rep a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister_ x = newRegister (pure x)

{-|
Like `put`, except the new value of the register is a pure value as opposed to the result of a parser.

@since 0.1.0.0
-}
put_ :: ParserOps rep => Reg r a -> rep a -> Parser ()
put_ r = put r . pure

{-|
@gets reg p@ first parses @p@ to get as a result, function @f@. Then, taking into account any changes
made during @p@, the value is fetched from @reg@ and applied to @f@.

@since 0.1.0.0
-}
gets :: Reg r a -> Parser (a -> b) -> Parser b
gets r p = p <*> get r

{-|
Like `gets`, except the adapter function is a pure argument as opposed to the result of a parser.

@since 0.1.0.0
-}
gets_ :: ParserOps rep => Reg r a -> rep (a -> b) -> Parser b
gets_ r = gets r . pure

{-|
@modify reg p@ first parses @p@ to collect the function @f@, then taking into account any changes
made during @f@, the value in @reg@ is modified using the function @f@ and put back into it.

@since 0.1.0.0
-}
modify :: Reg r a -> Parser (a -> a) -> Parser ()
modify r p = put r (gets r p)

{-|
Like `modify`, except the modification function is a pure argument as opposed to the result of a parser.

@since 0.1.0.0
-}
modify_ :: ParserOps rep => Reg r a -> rep (a -> a) -> Parser ()
modify_ r = modify r . pure

{-|
@move dst src@ takes the value stored in @src@ and additionally stores it into @dst@.

@since 0.1.0.0
-}
move :: Reg r1 a -> Reg r2 a -> Parser ()
move dst src = put dst (get src)

{-|
This combinator uses registers to emulate a restricted form of @(`>>=`)@: in a traditional monadic
setting, this would be considered to be the implementation:

> bind p f = p >>= f . pure

Essentially, the result of @p@ is available to be summoned purely as many times as needed. However,
it cannot be used to dynamically create structure: the selective combinators can be used to provide
that functionality partially.

@since 0.1.0.0
-}
bind :: Parser a -> (Parser a -> Parser b) -> Parser b
bind p f = newRegister p (f . get)

{-|
@local reg p q@ first parses @p@ and stores its value in @reg@ for the /duration/ of parsing @q@.
If @q@ succeeds, @reg@ will be restored to its original state /before/ @p@ was parsed.

@since 0.1.0.0
-}
local :: Reg r a -> Parser a -> Parser b -> Parser b
local r p q = bind (get r) $ \x -> put r p
                                *> q
                                <* put r x

{-|
This combinator will swap the values contained in two registers.

@since 0.1.0.0
-}
swap :: Reg r1 a -> Reg r2 a -> Parser ()
swap r1 r2 = bind (get r1) $ \x -> move r1 r2
                                *> put r2 x

{-|
@rollback reg p@ will perform @p@ and if it fails without consuming input, @reg@ will be restored
to its original state from /before/ @p@ was parsed, and the combinator will fail. If @p@ succeeds
the state in @reg@ will not be restored to an old version.

@since 0.1.0.0
-}
rollback :: Reg r a -> Parser b -> Parser b
rollback r p = bind (get r) $ \x -> p <|> put r x *> empty

{-|
This combinator is like a traditional imperative-style @for@-loop. Given @for init cond step body@,
@init@ is first parsed to initialise a register called @i@; the parser @cond@ is then performed to
check that the value in @i@ adheres to the predicate it returns; if so, then the @body@ is parsed,
@step@ modifies the state in @i@, and then the process repeats from @cond@ again. When @cond@ returns
@False@ for the predicate applied to @i@'s state, the loop terminates gracefully. If any component
of this parser fails the loop will fail.

@since 0.1.0.0
-}
for :: Parser a -> Parser (a -> Bool) -> Parser (a -> a) -> Parser () -> Parser ()
for init cond step body =
  newRegister init $ \i ->
    let cond' :: Parser Bool
        cond' = gets i cond
    in when cond' (while (body *> modify i step *> cond'))