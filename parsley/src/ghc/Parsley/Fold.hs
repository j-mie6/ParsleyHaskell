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
    chainl1', chainr1', chainPre, chainPost,
    pfoldr, pfoldl,
    pfoldr1, pfoldl1
  ) where

import Prelude hiding      (pure, (<*>), (<$>), (*>), (<*))
import Parsley.Alternative ((<|>), option)
import Parsley.Applicative (pure, (<*>), (<$>), (*>), (<*), (<:>), (<**>), void)
import Parsley.Internal    (Parser, Defunc(FLIP, ID, COMPOSE, EMPTY, CONS, CONST), ParserOps, pattern FLIP_H, pattern COMPOSE_H, pattern UNIT, chainPre, chainPost{-, loop-})
import Parsley.Register    (bind, get, modify, newRegister_)

{-chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre op p = newRegister_ ID $ \acc ->
  let go = modify acc (FLIP_H COMPOSE <$> op) *> go
       <|> get acc
  in go <*> p-}

{-chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost p op = newRegister p $ \acc ->
  let go = modify acc op *> go
       <|> get acc
  in go-}

-- Parser Folds
{-|
@pfoldr f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> many = pfoldr CONS EMPTY

@since 0.1.0.0
-}
pfoldr :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

{-|
@pfoldr1 f k p@ parses __one__ or more @p@s and combines the results using the function @f@. When @p@
fails without consuming input, the terminal result @k@ is returned.

> some = pfoldr1 CONS EMPTY

@since 0.1.0.0
-}
pfoldr1 :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
pfoldr1 f k p = f <$> p <*> pfoldr f k p

{-|
@pfoldl f k p@ parses __zero__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 0.1.0.0
-}
pfoldl :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) ((FLIP <$> pure f) <*> p)

{-|
@pfoldl1 f k p@ parses __one__ or more @p@s and combines the results using the function @f@. The
accumulator is initialised with the value @k@.

@since 0.1.0.0
-}
pfoldl1 :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser a -> Parser b
pfoldl1 f k p = chainPost (f <$> pure k <*> p) ((FLIP <$> pure f) <*> p)

-- Chain Combinators
{-|
@chainl1' wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /left/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the initial value from @p@ into the correct form.

@since 0.1.0.0
-}
chainl1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
chainl1' f p op = chainPost (f <$> p) (FLIP <$> op <*> p)

{-|
The classic version of the left-associative chain combinator. See 'chainl1''.

> chainl1 p op = chainl1' ID p op

@since 0.1.0.0
-}
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = chainl1' ID

{-|
@chainr1' wrap p op @ parses one or more occurrences of @p@, separated by @op@. Returns a value obtained
by a /right/ associative application of all functions returned by @op@ to the values returned by @p@.
The function @wrap@ is used to transform the final value from @p@ into the correct form.

@since 0.1.0.0
-}
chainr1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
chainr1' f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
           modify acc (FLIP_H COMPOSE <$> (op <*> x)) *> go
       <|> f <$> x
  in go <**> get acc

{-|
The classic version of the right-associative chain combinator. See 'chainr1''.

> chainr1 p op = chainr1' ID p op

@since 0.1.0.0
-}
chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = chainr1' ID

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
many = pfoldr CONS EMPTY

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
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . pfoldl CONST UNIT -- the void here will encourage the optimiser to recognise that the register is unused
--skipMany = flip loop (pure UNIT) . void -- This should be the optimal one, with register removed, but apparently not?! something is amiss, perhaps space leak?

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
sepEndBy1 p sep = newRegister_ ID $ \acc ->
  let go = modify acc (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p)
         *> (sep *> (go <|> get acc) <|> get acc)
  in go <*> pure EMPTY

{-sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1-}
