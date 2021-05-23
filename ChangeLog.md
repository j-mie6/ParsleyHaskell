# Revision history for `parsley`

## 0.1.0.0  -- 2021-05-22

* First version. Released on an unsuspecting world.

## 0.1.0.1  -- 2021-05-22

* Moved tests and benchmarks into a subproject, which will be easier later down the line.
* Removed useless `dump-core` flag (only used by test and bench, not by the library).
* Fleshed out README properly!

## 0.1.1.0  -- YYYY-mm-dd

* Added `IF_S`, `LAM_S` and `LET_S` to `Defunc`, which can be used with overloaded syntax
* Admin: Removed `idioms-plugin` from the test suite in favour of overloaded syntax from `lift-plugin`
* Admin: Switched to the `lift-plugin` implementation found in `parsley-garnish`