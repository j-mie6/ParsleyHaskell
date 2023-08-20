# Revision history for `parsley`

## 2.0.0.1 -- 2023-08-20

* Support for 9.6
* Removed use of `Text16` from the base API, it has been deprecated.

## 2.0.0.0 -- 2021-11-24

* Incorporated API naming conventions from _Design Patterns for Parser Combinators_.
    * `chainPre` -> `prefix`
    * `chainPost` -> `postfix`
    * `chainl1'` -> `infixl1`
    * `chainr1'` -> `infixr1`
    * `pfoldr` -> `manyr`
    * `pfoldl` -> `manyl`
    * `pfoldr1` -> `somer`
    * `pfoldl1` -> `somel`
* Reworked the `precedence` combinator system in line with the paper: the horrible overloading
  has gone now!
* Added in the `ParserOps` and `Debug` modules.
* Added `RANGES` to the `Defunc` API.
* Renamed `runParser` to `parse`.
* Moved some functionality to `Parsley.Char`.
* Added `digit`, `letter`, and `letterOrDigit`.

## 1.0.2.0 -- 2021-11-14

* Added `local_` combinator to `Register`.
* Added `localModify` and `localModify_` combinators to `Register`.

## 1.0.1.0 -- 2021-11-13

* Added `line` and `col` combinators.
* Added `pos` combinator.

## 1.0.0.3 -- 2021-10-29

* Support for `parsley-core-2.0.0` and `parsley-core-1.7.1`.
* Re-exports less from `parsley-core`, instead using (currently hidden) redefinition.

## 1.0.0.2 -- 2021-08-13

* Added small optimisation to accomodate new core changes: added `try` for all top-level parsers.

## 1.0.0.1 -- 2021-06-29

* Improved implementation of `oneOf` and `noneOf` to use ranges and not exhaustive character search

## 1.0.0.0 -- 2021-06-12

* Factored all of the `Parsley.Internal` modules out into `parsley-core` package

## 0.1.1.0  -- 2021-06-10

* Added `IF_S`, `LAM_S` and `LET_S` to `Defunc`, which can be used with overloaded syntax
* Admin: Removed `idioms-plugin` and `lift-plugin` from the test suite, depending on `parsley-garnish` instead
* Fixed building with GHC 9

## 0.1.0.1  -- 2021-05-22

* Moved tests and benchmarks into a subproject, which will be easier later down the line.
* Removed useless `dump-core` flag (only used by test and bench, not by the library).
* Fleshed out README properly!

## 0.1.0.0  -- 2021-05-22

* First version. Released on an unsuspecting world.
