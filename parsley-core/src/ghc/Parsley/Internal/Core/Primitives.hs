{-# LANGUAGE PatternSynonyms #-}
module Parsley.Internal.Core.Primitives (
    Parser,
    Reg,
    module Parsley.Internal.Core.Primitives
  ) where

import Prelude hiding                      (pure, (<*>))
import Parsley.Internal.Core.CombinatorAST (Combinator(..), ScopeRegister(..), Reg(..), Parser(..))
import Parsley.Internal.Core.Defunc        (Defunc(BLACK, ID, COMPOSE), pattern FLIP_H)
import Parsley.Internal.Common.Indexed     (Fix(In), (:+:)(..))
import Parsley.Internal.Common.Utils       (WQ)

{-|
This typeclass is used to allow abstraction of the representation of user-level functions.
See the instances for information on what these representations are. This may be required
as a constraint on custom built combinators that make use of one of the minimal required methods
of this class.

@since 0.1.0.0
-}
class ParserOps rep where
  {-|
  Lift a value into the parser world without consuming input or having any other effect.

  @since 0.1.0.0
  -}
  pure :: rep a -> Parser a

  {-|
  Attempts to read a single character matching the provided predicate. If it succeeds, the
  character will be returned and consumed, otherwise the parser will fail having consumed no input.

  @since 0.1.0.0
  -}
  satisfy :: rep (Char -> Bool) -- ^ The predicate that a character must satisfy to be parsed
          -> Parser Char        -- ^ A parser that matches a single character matching the predicate

  {-|
  @conditional fqs p def@ first parses @p@, then it will try each of the predicates in @fqs@ in turn
  until one of them returns @True@. The corresponding parser for the first predicate that succeeded
  is then executes, or if none of the predicates succeeded then the @def@ parser is executed.

  @since 0.1.0.0
  -}
  conditional :: [(rep (a -> Bool), Parser b)] -- ^ A list of predicates and their outcomes
              -> Parser a                      -- ^ A parser whose result is used to choose an outcome
              -> Parser b                      -- ^ A parser who will be executed if no predicates succeed
              -> Parser b

{-|
This is the default representation used for user-level functions and values: plain old code.

@since 0.1.0.0
-}
instance ParserOps WQ where
  pure = pure . BLACK
  satisfy = satisfy . BLACK
  conditional = conditional . map (\(f, t) -> (BLACK f, t))

{-|
This is used to allow defunctionalised versions of many standard Haskell functions to be used
directly as an argument to relevant combinators.

@since 0.1.0.0
-}
instance {-# INCOHERENT #-} x ~ Defunc => ParserOps x where
  pure = _pure
  satisfy = _satisfy
  conditional = _conditional

-- Core smart constructors
{-# INLINE _pure #-}
_pure :: Defunc a -> Parser a
_pure = Parser . In . L . Pure

{-|
Sequential application of one parser's result to another's. The parsers must both succeed, one after
the other to combine their results. If either parser fails then the combinator will fail.

@since 0.1.0.0
-}
infixl 4 <*>
(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (In (L (p :<*>: q)))

{-|
Sequence two parsers, keeping the result of the second and discarding the result of the first.

@since 0.1.0.0
-}
infixl 4 <*
(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (In (L (p :<*: q)))

{-|
Sequence two parsers, keeping the result of the first and discarding the result of the second.

@since 0.1.0.0
-}
infixl 4 *>
(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (In (L (p :*>: q)))

{-|
This combinator always fails.

@since 0.1.0.0
-}
empty :: Parser a
empty = Parser (In (L Empty))

{-|
This combinator implements branching within a parser. It is left-biased, so that if the first branch
succeeds, the second will not be attempted. In accordance with @parsec@ semantics, if the first
branch failed having consumed input the second branch cannot be taken. (see `try`)

@since 0.1.0.0
-}
infixr 3 <|>
(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (In (L (p :<|>: q)))

{-# INLINE _satisfy #-}
_satisfy :: Defunc (Char -> Bool) -> Parser Char
_satisfy = Parser . In . L . Satisfy

{-|
This combinator will attempt to parse a given parser. If it succeeds, the result is returned without
having consumed any input. If it fails, however, any consumed input remains consumed.

@since 0.1.0.0
-}
lookAhead :: Parser a -> Parser a
lookAhead = Parser . In . L . LookAhead . unParser

{-|
This combinator will ensure that a given parser fails. If the parser does fail, a @()@ is returned
and no input is consumed. If the parser succeeded, then this combinator will fail, however it will
not consume any input.

@since 0.1.0.0
-}
notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . In . L . NotFollowedBy . unParser

{-|
This combinator allows a parser to backtrack on failure, which is to say that it will
not have consumed any input if it were to fail. This is important since @parsec@ semantics demand
that the second branch of @(`<|>`)@ can only be taken if the first did not consume input on failure.

Excessive use of `try` will reduce the efficiency of the parser and effect the generated error
messages. It should only be used in one of two circumstances:

* When two branches of a parser share a common leading prefix (in which case, it is often better
  to try and factor this out).
* When a parser needs to be executed atomically (for example, tokens).

@since 0.1.0.0
-}
try :: Parser a -> Parser a
try = Parser . In . L . Try . unParser

{-# INLINE _conditional #-}
_conditional :: [(Defunc (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
_conditional cs (Parser p) (Parser def) =
  let (fs, qs) = unzip cs
  in Parser (In (L (Match p fs (map unParser qs) def)))

{-|
One of the core @Selective@ operations. The behaviour of @branch p l r@ is to first to parse
@p@, if it fails then the combinator fails. If @p@ succeeded then if its result is a @Left@, then
the parser @l@ is executed and applied to the result of @p@, otherwise @r@ is executed and applied
to the right from a @Right@.

Crucially, only one of @l@ or @r@ will be executed on @p@'s success.

@since 0.1.0.0
-}
branch :: Parser (Either a b) -- ^ The first parser to execute
       -> Parser (a -> c)     -- ^ The parser to execute if the first returned a @Left@
       -> Parser (b -> c)     -- ^ The parser to execute if the first returned a @Right@
       -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (In (L (Branch c p q)))

{-|
This combinator parses repeated applications of an operator to a single final operand. This is
primarily used to parse prefix operators in expressions.

@since 0.1.0.0
-}
chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre op p =
  newRegister (pure ID) (\r ->
    loop (put r (pure (FLIP_H COMPOSE) <*> op <*> get r))
         (get r))
  <*> p

{-|
This combinator parses repeated applications of an operator to a single initial operand. This is
primarily used to parse postfix operators in expressions.

@since 0.1.0.0
-}
chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost p op =
  newRegister p $ \r ->
    loop (put r (op <*> get r))
         (get r)

{-|
The combinator @loop body exit@ parses @body@ zero or more times until it fails. If the final @body@
failed having not consumed input, @exit@ is performed, otherwise the combinator fails:

> loop body exit = let go = body *> go <|> exit in go

@since 1.1.0.0
-}
loop :: Parser () -> Parser a -> Parser a
loop (Parser body) (Parser exit) = Parser (In (L (Loop body exit)))

{-|
Creates a new register initialised with the value obtained from parsing the first
argument. This register is provided to the second argument, a function that generates a parser
depending on operations derived from the register. This parser is then performed.

Note: The rank-2 type here serves a similar purpose to that in the @ST@ monad. It prevents the
register from leaking outside of the scope of the function, safely encapsulating the stateful
effect of the register.

@since 0.1.0.0
-}
newRegister :: Parser a                        -- ^ Parser with which to initialise the register
            -> (forall r. Reg r a -> Parser b) -- ^ Used to generate the second parser to execute
            -> Parser b
newRegister (Parser p) f = Parser (In (R (ScopeRegister p (unParser . f))))

{-|
Fetches a value from a register and returns it as its result.

@since 0.1.0.0
-}
get :: Reg r a -> Parser a
get (Reg reg) = Parser (In (L (GetRegister reg)))

{-|
Puts the result of the given parser into the given register. The old value in the register will be
lost.

@since 0.1.0.0
-}
put :: Reg r a -> Parser a -> Parser ()
put (Reg reg) (Parser p) = Parser (In (L (PutRegister reg p)))

{-|
This combinator can be used to debug parsers that have gone wrong. Simply
wrap a parser with @debug name@ and when that parser is executed it will
print a debug trace on entry and exit along with the current context of the
input.

@since 0.1.0.0
-}
debug :: String   -- ^ The name that identifies the wrapped parser in the debug trace
      -> Parser a -- ^ The parser to track during execution
      -> Parser a
debug name (Parser p) = Parser (In (L (Debug name p)))