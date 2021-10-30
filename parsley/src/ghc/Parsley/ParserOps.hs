module Parsley.ParserOps (module Parsley.ParserOps) where

import Prelude hiding (pure)
import Control.Arrow    (first)
import Parsley.Internal (Parser, WQ, Defunc(BLACK))

import qualified Parsley.Internal as Internal (pure, satisfy, conditional)

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
  conditional = conditional . map (first BLACK)

{-|
This is used to allow defunctionalised versions of many standard Haskell functions to be used
directly as an argument to relevant combinators.

@since 0.1.0.0
-}
instance {-# INCOHERENT #-} x ~ Defunc => ParserOps x where
  pure = Internal.pure
  satisfy = Internal.satisfy
  conditional = Internal.conditional