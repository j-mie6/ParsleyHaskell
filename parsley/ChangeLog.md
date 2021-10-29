# Revision history for `parsley`

## 0.1.0.0  -- 2021-05-22

* First version. Released on an unsuspecting world.

## 0.1.0.1  -- 2021-05-22

* Moved tests and benchmarks into a subproject, which will be easier later down the line.
* Removed useless `dump-core` flag (only used by test and bench, not by the library).
* Fleshed out README properly!

## 0.1.1.0  -- 2021-06-10

* Added `IF_S`, `LAM_S` and `LET_S` to `Defunc`, which can be used with overloaded syntax
* Admin: Removed `idioms-plugin` and `lift-plugin` from the test suite, depending on `parsley-garnish` instead
* Fixed building with GHC 9

## 1.0.0.0 -- 2021-06-12

* Factored all of the `Parsley.Internal` modules out into `parsley-core` package

## 1.0.0.1 -- 2021-06-29

* Improved implementation of `oneOf` and `noneOf` to use ranges and not exhaustive character search

## 1.0.0.2 -- 2021-08-13

* Added small optimisation to accomodate new core changes: added `try` for all top-level parsers.

## 1.0.0.3 -- TBD

* Support for `parsley-core-2.0.0` and `parsley-core-1.7.1`.
* Re-exports less from `parsley-core`, instead using (currently hidden) redefinition.