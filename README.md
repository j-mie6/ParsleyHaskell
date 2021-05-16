# Parsley ![GitHub Workflow Status](https://img.shields.io/github/workflow/status/j-mie6/ParsleyHaskell/CI) ![GitHub release](https://img.shields.io/github/v/release/j-mie6/ParsleyHaskell?include_prereleases&sort=semver) [![GitHub license](https://img.shields.io/github/license/j-mie6/ParsleyHaskell.svg)](https://github.com/j-mie6/ParsleyHakell/blob/master/LICENSE)

## What is Parsley?
Parsley is a very fast parser combinator library that outperforms the other libraries in both the
parsec family, as well as Happy. To make this possible, it makes use of Typed Template Haskell
to generate the code for the parsers.

## How do I use it?

TODO

### Examples

TODO

### How does Parsley being a _Staged Selective_ library change its use?

TODO

## How does it work?

TODO

## Bug Reports
If you encounter a bug when using Parsley, try and minimise the example of the parser (and the input) that triggers the bug.
If possible, make a self contained example: this will help me to identify the issue without too much issue.

## References
* This work spawned a paper at ICFP 2020: [**Staged Selective Parser Combinators**](https://dl.acm.org/doi/10.1145/3409002)