# Parsley ![GitHub Workflow Status](https://img.shields.io/github/workflow/status/j-mie6/ParsleyHaskell/CI) ![GitHub release](https://img.shields.io/github/v/release/j-mie6/ParsleyHaskell?include_prereleases&sort=semver) [![GitHub license](https://img.shields.io/github/license/j-mie6/ParsleyHaskell.svg)](https://github.com/j-mie6/ParsleyHakell/blob/master/LICENSE)

## What is Parsley?
Parsley is a very fast parser combinator library that outperforms the other libraries in both the
parsec family, as well as Happy. To make this possible, it makes use of Typed Template Haskell
to generate the code for the parsers.

## How do I use it? ![Hackage Version](https://img.shields.io/hackage/v/parsley)
Parsley is distributed on Hackage, and can be added by depending on the package `parsley`.

The version policy adheres to the regular Haskell PVP, but the two major versions are distinguished
in Parsley: the first is the _User API_ major version, which represents backwards incompatible changes
in the regular PVP sense that could affect any users of the library; the second version is the
_Internal API_ major version, which would only effect users who use part of the internal parsley
modules. As such, for people that are **not** explicitly importing anything from `Parsley.Internal`, or
its submodules, the second major version does not matter: `0.2.0.0` and `0.3.0.0` would be compatible,
for instance.

To use it, you'll need to write you parsers in another file from where they will be used: this is
due to Template Haskell.

<!--### Examples

TODO-->

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

```haskell
data WQ a = WQ a (Code a)
```

This gives us combinators like:

```haskell
pure :: WQ a -> Parser a
satisfy :: WQ a -> Parser a

char :: Char -> Parser a
char c = satisfy (WQ (== c) [||(== c)||])
```

Using `WQ` explicitly like this can get annoying, which is what the `lift-plugin` and the
`idioms-plugin` are both for: versions compatible with Parsley can be found on my GitHub, and the
`cabal.project` in this repo shows how these should be installed until they are properly released.

## How does it work?
In short, Parsley represents all parsers as Abstract Syntax Trees (ASTs). The representation of the
parsers the users write is called the Combinator Tree, which is analysed and optimised by Parsley.
This representation is then transformed into an Abstract Machine in CPS form, this is analysed further
before being partially evaluated at compile-time to generate high quality Haskell code. For the long
version, I'd recommend checking out the paper!

## Bug Reports
If you encounter a bug when using Parsley, try and minimise the example of the parser (and the input)
that triggers the bug. If possible, make a self contained example: this will help me to identify the
issue without too much issue. It might be helpful to import `Parsley.Internal.Verbose` to provide a
debug dump that I can check out.

## References
* This work spawned a paper at ICFP 2020: [**Staged Selective Parser Combinators**](https://dl.acm.org/doi/10.1145/3409002)