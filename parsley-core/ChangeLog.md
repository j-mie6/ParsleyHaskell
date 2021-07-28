# Revision history for `parsley-core`

## 1.0.0.0 -- 2021-06-12

* First version. Released on an unsuspecting world.
* Core factored out of the main `parsley` package

## 1.0.1.0 -- 2021-06-26

* Introduced `Lam` to the API and conversion functions for `Core.Defunc`
* Extra type ascriptions added to generated code

## 1.0.1.1 -- 2021-06-27

* Added input factoring to `try p <|> q` and also forms with `f <$> try p <|> q` and `try p $> x <|> q`

## 1.1.0.0 -- 2021-07-01

* Switched both backends to make use of `Lam` instead of `Core.Defunc`, reducing burden on GHC
* Added duplication avoidance optimisation when value to be duplicated is `Lam.Var True`

## 1.2.0.0 -- 2021-07-01

* For GHC 8.10+, leveraged the static structure of functions:
  * Handlers are now static functions, reducing the beta-reduction required by GHC, `fatal` now generates better code
  * Return continuations are also static functions, reducing beta-reduction required by GHC, `halt` generates better code
  * Recursive calls are also static functions, removing a lot of junk with the conversion from iterators to recursion
* Registers are now bound once for recursive parsers, which close over their free-registers
* Strictness has been updated to reflect the reduced burden on GHC to optimise: now strictness is for performance, and
  not to coax GHC to optimise at the cost of performance
* Removed the "bad" binding for `Sat`, handlers are always bound on creation, so the binding is basically meaningless
* Performance on 8.10+ is anywhere from 10-20% faster than 1.1.0.0

## 1.2.0.1 -- 2021-07-03

* Added Jump-Elision optimisation to the code generator.

## 1.3.0.0 -- 2021-07-03

* Improved the `Lam` reduction algorithm
* Preliminary support for `if true` reduction from `item` and `const True`
* Introduced `_if` and `ap` in `Machine.Defunc`, removed `genDefunc1`

## 1.4.0.0 -- 2021-07-22
NOTE: The API exposed to `parsley` has changed, however, the changed types match up
and the underlying types are not exposed. This means that `parsley` cannot write
the type down to begin with, so the API change does not _actually_ result in any
backward incompatiblity _unless_ the `Parsley.Internal.*` modules are imported:
this meets requirements for internal major change.

* Removed an `unsafeCoerce` from register creation, using more existentials.
* Changed `CharList`'s `more` check to test for `[]` and not length (faster!)
* Added static information to offset in the machine
* Leveraged static information to refine handlers at compile time, offering up
  to 20% performance improvement
* Code restructuring and refactoring
* Added copious amounts of documentation

## 1.5.0.0 -- TBD
Infrastructure for improved handler analysis:

* Refactored `LetBinding` to include more generic metadata.
* Added metadata to `StaSubroutine` and introduced `StaSubroutine#` and associated functions.
* Fed metadata through `letRec`'s `genBinding` and into `buildRec`.
* Added an `Amount` to `Offset`, which also takes into account a multiplicity, used to track unknown
  but non-zero quantities.
* Added `callCC` and modified the API for `suspend` to allow for abstracted `Offset` creation. The
  `callCC` operation promises to utilise static input consumption from the subroutine to refine the
  input to the return continuation (making use of the multiplicity above).
* Refactored the `CombinatorAnalyser` into an `Analysis.Cut` module (and moved `Dependencies` there too)
* Refactored the `InstructionAnalyser` into an `Analysis.Coins` and `Analysis.Relevancy` modules
* More documentation

Input Reclamation:

* Added `Machine.Types.Coins`, which separates coins for length checks from input reclamation.
* `Analysis.Coins` now deals wiith the `Coins` type, as do the instructions.
* Added `Common.RewindQueue` to handle rewindable input caching.
* Moved the implementation of `Queue` into a `Queue.Impl` submodule, for `RewindQueue` and testing.