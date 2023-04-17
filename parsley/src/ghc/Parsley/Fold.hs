{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Fold
Description : The "folding" combinators: chains and iterators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the combinator concerned with some form of iteration or input folding. Notably,
this includes the traditional `many` and `some` combinators.

@since 0.1.0.0
-}
module Parsley.Fold (
    many, some, manyN,
    skipMany, skipSome, skipManyN, --loop,
    sepBy, sepBy1, endBy, endBy1, sepEndBy, sepEndBy1,
    chainl1, chainr1, chainl, chainr,
    infixl1, infixr1, prefix, postfix,
    manyr, manyl,
    somer, somel
  ) where

import Prelude hiding           (pure, (<*>), (<$>), (*>), (<*))
import Parsley.Alternative      ((<|>), option)
import Parsley.Applicative      (pure, (<*>), (<$>), (*>), (<*), (<:>), (<**>), void)
import Parsley.Defunctionalized (Defunc(FLIP, ID, COMPOSE, EMPTY, CONS, CONST), pattern FLIP_H, pattern UNIT)
import Parsley.Internal         (Parser)
import Parsley.ParserOps        (ParserOps)
import Parsley.Register         (get, modify, newRegister)

import qualified Parsley.Internal as Internal (loop)

{-|
The combinator @loop body exit@ parses @body@ zero or more times until it fails. If the final @body@
failed having not consumed input, @exit@ is performed, otherwise the combinator fails:

> loop body exit = let go = body *> go <|> exit in go

@since 2.0.0.0
-}
loop :: Parser () -> Parser a -> Parser a
loop = Internal.loop

{-|
This combinator parses repeated applications of an operator to a single final operand. This is
primarily used to parse prefix operators in expressions.

@since 2.0.0.0
-}
prefix :: Parser (a -> a) -> Parser a -> Parser a
prefix op p = postfix (pure ID) (FLIP_H COMPOSE <$> op) <*> p

{-|
This combinator parses repeated applications of an operator to a single initial operand. This is
primarily used to parse postfix operators in expressions.

@since 2.0.0.0
-}
postfix :: Parser a -> Parser (a -> a) -> Parser a
postfix p op =
  newRegister p $ \r ->
    loop (modify r op)
         (get r)

-- Parser Folds
{-|
@manyr f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> many = manyr CONS EMPTY

@since 2.0.0.0
-}
manyr :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
manyr f k p = prefix (f <$> p) (pure k)

{-|
@somer f k p@ parses __one__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> some = somer CONS EMPTY

@since 2.0.0.0
-}
somer :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
somer f k p = f <$> p <*> manyr f k p

{-|
@manyl f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 2.0.0.0
-}
manyl :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
manyl f k p = postfix (pure k) ((FLIP <$> pure f) <*> p)

{-|
@somel f k p@ parses __one__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 2.0.0.0
-}
somel :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
somel f k p = postfix (f <$> pure k <*> p) ((FLIP <$> pure f) <*> p)

-- Chain Combinators
{-|
@infixl1 wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /left/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the initial value from @p@ into the correct form.

@since 2.0.0.0
-}
infixl1 :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
infixl1 wrap p op = postfix (wrap <$> p) (FLIP <$> op <*> p)

{-|
The classic version of the left-associative chain combinator. See 'infixl1'.

> chainl1 p op = infixl1 ID p op

@since 0.1.0.0
-}
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = infixl1 ID

{-|
@infixr1 wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /right/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the final value from @p@ into the correct form.

@since 2.0.0.0
-}
infixr1 :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
infixr1 wrap p op = let go = p <**> (FLIP <$> op <*> go <|> pure wrap) in go

{-|
The classic version of the right-associative chain combinator. See 'infixr1'.

> chainr1 p op = infixr1 ID p op

@since 0.1.0.0
-}
chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = infixr1 ID

{-|
Like `chainr1`, but may parse zero occurences of @p@ in which case the value is returned.

@since 0.1.0.0
-}
chainr :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainr p op x = option x (chainr1 p op)

{-|
Like `chainl1`, but may parse zero occurences of @p@ in which case the value is returned.

@since 0.1.0.0
-}
chainl :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainl p op x = option x (chainl1 p op)

-- Derived Combinators
{-|
Attempts to parse the given parser __zero__ or more times, collecting all of the successful results
into a list. Same as @manyN 0@

@since 0.1.0.0
-}
many :: Parser a -> Parser [a]
many = manyr CONS EMPTY

{-|
Attempts to parse the given parser __n__ or more times, collecting all of the successful results
into a list.

@since 0.1.0.0
-}
manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

{-|
Attempts to parse the given parser __one__ or more times, collecting all of the successful results
into a list. Same as @manyN 1@

@since 0.1.0.0
-}
some :: Parser a -> Parser [a]
some = manyN 1

{-|
Like `many`, excepts discards its results.

@since 0.1.0.0
-}
skipMany :: Parser a -> Parser ()
--skipMany p = loop (void p) unit
skipMany = void . manyl CONST UNIT -- This is still faster, the above generates better code, but GHC starts doing weird things!

{-|
Like `manyN`, excepts discards its results.

@since 0.1.0.0
-}
skipManyN :: Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

{-|
Like `some`, excepts discards its results.

@since 0.1.0.0
-}
skipSome :: Parser a -> Parser ()
skipSome = skipManyN 1

{-|
@sepBy p sep@ parses __zero__ or more occurrences of @p@, separated by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = option EMPTY (sepBy1 p sep)

{-|
@sepBy1 p sep@ parses __one__ or more occurrences of @p@, separated by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

{-|
@endBy p sep@ parses __zero__ or more occurrences of @p@, separated and ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

{-|
@endBy1 p sep@ parses __one__ or more occurrences of @p@, separated and ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
endBy1 :: Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

{-|
@sepEndBy p sep@ parses __zero__ or more occurrences of @p@, separated and /optionally/ ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepEndBy :: Parser a -> Parser b -> Parser [a]
sepEndBy p sep = option EMPTY (sepEndBy1 p sep)

{-|
@sepEndBy1 p sep@ parses __one__ or more occurrences of @p@, separated and /optionally/ ended by @sep@.
Returns a list of values returned by @p@.

@since 0.1.0.0
-}
sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep =
  let seb1 = p <:> option EMPTY (sep *> option EMPTY seb1)
  in seb1
