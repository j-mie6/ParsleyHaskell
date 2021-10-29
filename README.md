# Parsley ![GitHub Workflow Status](https://img.shields.io/github/workflow/status/j-mie6/ParsleyHaskell/CI) ![GitHub release](https://img.shields.io/github/v/release/j-mie6/ParsleyHaskell) [![GitHub license](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://github.com/j-mie6/ParsleyHaskell/blob/master/LICENSE) ![GitHub commits since latest release (by SemVer)](https://img.shields.io/github/commits-since/j-mie6/ParsleyHaskell/latest)

## What is Parsley?
Parsley is a very fast parser combinator library that outperforms the other libraries in both the
parsec family, as well as Happy. To make this possible, it makes use of Typed Template Haskell
to generate the code for the parsers.

## How do I use it? [![Hackage Version](https://img.shields.io/hackage/v/parsley)](https://hackage.haskell.org/package/parsley) ![Dependent repos (via libraries.io)](https://img.shields.io/librariesio/dependent-repos/hackage/parsley)
Parsley is distributed on [Hackage](https://hackage.haskell.org/package/parsley), and can be added by depending on the package `parsley`.

The version policy for `parsley-core` adheres to the regular Haskell PVP, but the two major versions are distinguished: the first is the _Public API_ major version, which represents backwards incompatible changes
in the regular PVP sense that could affect `parsley` itself (note `parsley` _only_ imports from `Parsley.Internal` itself); the second version is the
_Internal API_ major version, which would only effect users who use part of the internal parsley
modules. As such, for people that are **not** explicitly importing anything from `Parsley.Internal.*`, the second major version does not matter: `0.2.0.0` and `0.3.0.0` would be compatible, for instance.

To use it, you'll need to write you parsers in another file from where they will be used: this is
due to Template Haskell.

### How does Parsley being a _Staged Selective_ library change its use?
By being a _Selective_ Parser Combinator library, Parsley does not support monadic operations such
as `(>>=)` or `return`. Instead, the most powerful operations are `select` or `branch`. Most monadic
power can be recovered using the functionality provided by `Parsley.Register`, as well as the
selectives.

The reason monads are not supported is because of the _Staging_: Parsley parsers are compiled ahead
of time to produce fast code, but this means the entirety of the parser must be known before any
input is provided, ruling out dynamic monadic operations. The use of staging (in this instance provided
by Typed Template Haskell) means that the signatures of the combinators do not correspond to their
counterparts in other libraries: they don't use raw values, they use code of values. A consequence
of this is that Parsley does not implement instances of `Functor`, `Applicative`, `Alternative`,
or indeed `Selective`; `do`-notation also cannot be used even with `ApplicativeDo`, except perhaps
if `RebindableSyntax` is used.

Code is provided to the combinators by way of the datatype `WQ` (or `Defunc` if you're feeling fancy),
which pairs a normal value with its Haskell code representation:

```hs
data WQ a = WQ a (Code a)
```

This gives us combinators like:

```hs
pure :: WQ a -> Parser a
satisfy :: WQ a -> Parser a

char :: Char -> Parser a
char c = satisfy (WQ (== c) [||(== c)||])
```

Using `WQ` explicitly like this can get annoying, which is what the `parsley-garnish` package is for!
Currently, the garnish provides one plugin called `OverloadedQuotes`, which replaces the behaviour of
the default _Untyped_ Template Haskell quotes in a file so that they produce one of `WQ` or `Defunc`.
See the `Parsley.OverloadedQuotesPlugin` module in the [`parsley-garnish`](https://hackage.haskell.org/package/parsley-garnish) package for more information.

## How does it work?
In short, Parsley represents all parsers as Abstract Syntax Trees (ASTs). The representation of the
parsers the users write is called the Combinator Tree, which is analysed and optimised by Parsley.
This representation is then transformed into an Abstract Machine in CPS form, this is analysed further
before being partially evaluated at compile-time to generate high quality Haskell code. For the long
version, I'd recommend checking out the paper!

## Bug Reports
If you encounter a bug when using Parsley, try and minimise the example of the parser (and the input)
that triggers the bug. If possible, make a self contained example: this will help me to identify the
issue without too much issue. It might be helpful to import `parsley-core:Parsley.Internal.Verbose` to provide a
debug dump that I can check out.

## References
* This work spawned a paper at ICFP 2020: [**Staged Selective Parser Combinators**](https://dl.acm.org/doi/10.1145/3409002)

### Talks
For talks on how writing parsers changes when using Parsley see either of these:
* [*Garnishing Parsec with Parsley*](https://www.youtube.com/watch?v=tJcyY9L2z84) - Berlin Functional Programming Group, January 2021
* [*Exploring Parsley: Working with Staged Selective Parsers*](https://www.youtube.com/watch?v=Zhu-cPY1eac) - MuniHac 2020

For the technical overview of how Parsley works:
* [*Staged Selective Parser Combinators*](https://www.youtube.com/watch?v=lH65PvRgm8M) - ICFP 2020
