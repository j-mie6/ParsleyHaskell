```

                   ██╗   ██╗ ██████╗ ██████╗  █████╗
                   ╚██╗ ██╔╝██╔═══██╗██╔══██╗██╔══██╗
                    ╚████╔╝ ██║   ██║██║  ██║███████║
                     ╚██╔╝  ██║   ██║██║  ██║██╔══██║
                      ██║   ╚██████╔╝██████╔╝██║  ██║
                      ╚═╝    ╚═════╝ ╚═════╝ ╚═╝  ╚═╝

                  parser combinators for young padawans

```

Introduction
============

Yoda is a small parser combinator library. It is not efficient, nor
beautiful, but it hopes to teach young padawans to use the source
and learn to write a parser.

    ╔═════════════════════════════════════════════════════════════╗
    ║                                                             ║
    ║  <(-,-)>  Do, or do not, there is no try.  -- Master Yoda   ║
    ║                                                             ║
    ╚═════════════════════════════════════════════════════════════╝

Yoda is a parser in the Parsec family of libraries, which includes
Parsec, attoparsec, Megaparsec, and trifecta. The main difference is
that Yoda does not require you to use the `try` function: it
automatically tries all alternatives for you.

The module exports the following functions and types. Some of these
functions are defined outside of this file, namely, those marked under
`Functor`, `Applicative`, `Alternative`, `Monad`.

```lhs

> {-# LANGUAGE InstanceSigs #-}
> module Yoda
>   ( Parser
>   , parse
>   , parseMaybe
>   , parseIO
>
>   -- Functor
>   , (<$>), (<$), skip
>
>   -- Applicative
>   , pure, (<*>), (<*), (*>), (<**>)
>
>   -- Alternative
>   , (<|>), empty, some, many, optional, choice
>   , chainl, chainl1, chainr, chainr1
>   , prefix, postfix

>   -- Monoidal
>   , unit, mult, (<~>), (<~), (~>)
>
>   -- Monad
>   , return, (>>=)
>
>   -- Miscellaneous
>   , item, look, eof, char, string, satisfy
>   , oneOf, noneOf, sepBy, sepBy1
>   , (<:>)
>
>   , cull
>   , try  -- not needed, but here for historic reasons
>
>   ) where

```

We have to import some classes whose instances we will be
implementing for our parsers.
```lhs

> import Control.Monad
> import Control.Applicative
> import Data.List

```

Parser
======

Our parsers will take in a `String` and produce a list of possible
parses, along with remaining unparsed strings.
```lhs

> newtype Parser a = Parser (String -> [(a, String)])

> parse :: Parser a -> (String -> [(a, String)])
> parse (Parser p) = p

```

```

> parseIO :: Parser a -> String -> IO a
> parseIO p fileName = do
>   file <- readFile fileName
>   let Just result = parseMaybe p file
>   return result

> parseMaybe :: Parser a -> String -> Maybe a
> parseMaybe px ts = case parse px ts of
>   []             -> Nothing
>   ((x, ts'):txs) -> Just x

```
This parser tries to push out a character from the incoming stream. It
fails to parse if there is no remaining input.
```lhs

> item :: Parser Char
> item = Parser (\ts -> case ts of
>   []      -> []
>   (t:ts') -> [(t, ts')])

```
Now we implement Luke, I mean, look:
```lhs

> look :: Parser String
> look = Parser (\ts -> [(ts, ts)])

```
It is also useful to know if we have reached the end of the input:
```lhs

> eof :: Parser ()
> eof = Parser (\ts -> case ts of
>   [] -> [((), ts)]
>   _  -> [])

```
At this stage, we can output what has been given to us on the input,
but we have no way to change the outcome of what we do based on that
input.

We'll now start climbing the class hierarchy. Each class provides its
own ways of combining and working with parsers, and extends the power
of our combinator language with new functionality.


Functor
=======

The functor instance captures the idea of modifying the output of
successful parses.
```lhs

> instance Functor Parser where
>   fmap :: (a -> b) -> Parser a -> Parser b
>   fmap f (Parser px) = Parser (\ts -> [ (f x, ts') | (x, ts') <- px ts])

```
Derived combinators:
```lhs

< (<$>) :: Functor f => (a -> b) -> f a -> f b
< (<$>) = fmap
<
< (<$) :: Functor f => a -> f b -> f a
< x <$ py = const x <$> py

> skip :: Functor f => f a -> f ()
> skip px = () <$ px

```

Applicative
===========

The applicative instance shows how parsers can be chained together.
```lhs

> instance Applicative Parser where
>   pure :: a -> Parser a
>   pure x = Parser (\ts -> [(x, ts)])
>
>   (<*>) :: Parser (a -> b) -> Parser a -> Parser b
>   Parser pf <*> Parser px =
>     Parser (\ts -> [ (f x, ts'') | (f, ts')  <- pf ts
>                                  , (x, ts'') <- px ts'])

```
Derived combinators:
```lhs

< (<*) :: Applicative f => f a -> f b -> f a
< px <* py = const <$> px <*> py
<
< (*>) :: Applicative f => f a -> f b -> f b
< px *> py = flip const <$> px <*> py
<       -- = id <$ px <*> py
<
< (<**>) :: Applicative f => f a -> f (a -> b) -> f b
< px <**> pf = (flip ($)) <$> px <*> pf


> (<:>) :: Applicative f => f a -> f [a] -> f [a]
> px <:> pxs = (:) <$> px <*> pxs

> between :: Applicative f => f open -> f close -> f a -> f a
> between popen pclose px = popen *> px <* pclose

```

Monoidal
========

An equivalent alternative class to `Applicative` is `Monoidal`.
```lhs

> class Functor f => Monoidal f where
>   unit :: f ()
>   mult :: f a -> f b -> f (a, b)

> instance Monoidal Parser where

```
The `unit` parser returns `()` without parsing any input.
```lhs

>   unit :: Parser ()
>   unit = Parser (\ts -> [((), ts)])

```
For example:
```lhs

< parse (unit) "Hello" = [((), "Hello")]

```
The `mult` combinator takes two parsers `px` and `py` and returns
pairs of values containing the results of parsing `px` followed by
`py`.
```lhs

>   mult :: Parser a -> Parser b -> Parser (a, b)
>   mult (Parser px) (Parser py) =
>     Parser (\ts -> [((x, y), ts'') | (x, ts')  <- px ts
>                                    , (y, ts'') <- py ts'])

```
This is convenient as the following binary operator:
```lhs

> (<~>) :: Monoidal f => f a -> f b -> f (a, b)
> px <~> py =  mult px py

```
The following derived combinators project out an element of the pair:
```lhs

> (<~) :: Monoidal f => f a -> f b -> f a
> px <~ py = fst <$> px <~> py
>
> (~>) :: Monoidal f => f a -> f b -> f b
> px ~> py = snd <$> px <~> py

```
The combinators for `Applicative` and `Monoidal` can be defined in
terms of one another.
```lhs

< pure x    = const x <$> unit
< pf <*> px = uncurry ($) (pf <~> py)

< unit       = pure ()
< mult px py = (,) <$> px <*> py

< px <* py  = px <~ py
< px *> py  = px ~> py

```

Alternative
===========

Choices between parsers are given by the `Alternative` class. This
class assumes that the given Parser is already `Applicative`.
```lhs

> instance Alternative Parser where
>   empty :: Parser a
>   empty = Parser (\ts -> [])
>
>   (<|>) :: Parser a -> Parser a -> Parser a
>   Parser px <|> Parser py = Parser (\ts -> px ts ++ py ts)

```

Derived combinators
-------------------

A simple convenience function that offers the choice between inputs is
given by `choice`:
```lhs

> choice :: Alternative f => [f a] -> f a
> choice = foldr (<|>) empty

```

It's useful to repeat a parser multiple times. The `some px` parser
parses one or more instances of `px`, whereas the `many px` parser
parses zero or more instances of `px`.
```lhs

< some :: Alternative f => f a -> f [a]
< some px = px <:> many px
<
< many :: Alternative f => f a -> f [a]
< many px = some px <|> pure []

```

Giving the option to parse:

< optional :: Alternative f => f a -> f (Maybe a)
< optional v = Just <$> v <|> pure Nothing


```lhs

> chainl :: Alternative f => f a -> f (a -> a -> a) -> a -> f a
> chainl px pf x = chainl1 px pf <|> pure x

> chainl1 :: Alternative f => f a -> f (a -> a -> a) -> f a
> chainl1 px pf = foldl' (flip ($)) <$> px <*> (many (flip <$> pf <*> px))

> chainr :: Alternative f => f a -> f (a -> a -> a) -> a -> f a
> chainr px pf x = chainr1 px pf <|> pure x

> chainr1 :: Alternative f => f a -> f (a -> a -> a) -> f a
> chainr1 px pf = flip (foldr ($)) <$> (many (px <**> pf)) <*> px

> prefix :: Alternative f => f (a -> a) -> f a -> f a
> prefix op p = flip (foldr ($)) <$> many op <*> p

> postfix :: Alternative f => f a -> f (a -> a) -> f a
> postfix p op = foldl (flip ($)) <$> p <*> many op

> sepBy  :: Alternative f => f a -> f sep -> f [a]
> sepBy px psep = sepBy1 px psep <|> pure []
>
> sepBy1 :: Alternative f => f a -> f sep -> f [a]
> sepBy1 px psep = px <:> (many (psep *> px))

```

Monad
=====

The monad instance allows the value in the result of one parser to
influence the output of the parse.
```lhs

> instance Monad Parser where
>   return :: a -> Parser a
>   return ofTheJedi = pure ofTheJedi   -- sorry, I couldn't help it.
>
>   (>>=) :: Parser a -> (a -> Parser b) -> Parser b
>   Parser px >>= f = Parser (\ts -> concat [ parse (f x) ts' | (x, ts') <- px ts ])


Satisfy
=======

The `satisfy` parser accepts characters that satisfy a given
predicate. It can be derived from the monadic interface as
follows:

```
Derived combinators:
```lhs

< satisfy :: (Char -> Bool) -> Parser Char
< satisfy p = item >>= \t -> if p t then pure t else empty

```

More directly, we can avoid monadic combinators with this:

```lhs

> satisfy :: (Char -> Bool) -> Parser Char
> satisfy p = Parser (\ts -> case ts of
>   []      -> []
>   (t:ts') -> [(t, ts') | p t])
>
> oneOf :: [Char] -> Parser Char
> oneOf = satisfy . flip elem
>
> noneOf :: [Char] -> Parser Char
> noneOf cs = satisfy (not . flip elem cs)

```
Using `satisfy` we can build a useful array of smaller parsers, such
as one for recognising a particular character, or a particular string.
```lhs

> char :: Char -> Parser Char
> char c = satisfy (c ==)

>
> string :: String -> Parser String
> string []     = return ""
> string (c:cs) = char c <:> string cs

```

Miscellaneous
=============

It is convenient to have a way to remove results from a parse.
```lhs

> cull :: Parser a -> Parser a
> cull (Parser px) = Parser (\ts -> take 1 (px ts))

```


There is a try after all, but it is only here to make this work with
code written for other members of the Parsec family.
```lhs

> try :: Parser a -> Parser a
> try = id

```



Pronunciation    /prəˌnʌnsɪˈeɪʃ(ə)n/
====================================

Most of the symbols in this file are not easily pronounced, so let's establish
some nomenclature.

    Symbol   Name

    <$>      fmap
    <$       const fmap

    <*>      tie fighter, or just "tie", ap
    <*       tie left,
    *>       tie right,
    <**>     tie bomber, pa

    >>=      bind

    <|>      or

    <:>      lift cons

