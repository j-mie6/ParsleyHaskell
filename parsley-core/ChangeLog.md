# Revision history for `parsley-core`

## 2.2.0.1 -- 2023-04-26

* Improved the free register analysis by reimplementing in terms of lambda-lifting algorithms.

## 2.2.0.0 -- 2022-08-03

* Removed `RangeSet`, as this now resides in `rangeset`.

## 2.1.0.1 -- 2022-06-01

* Added normalisation rule for lets in `Lam`.
* Added GHC 9.2 support.

## 2.1.0.0 -- 2022-01-12

* Added `RangeSet` datastructure.
* Added `Pos` module for static manipulation of position information.
* Added `CharPred` as a specialised defunctionalisation of `Char -> Bool` functions.
* Moved `InputCharacteristic` to its own module.
* Use `CharPred` for `Sat` and `Satisfy`.
* Simplified the interface for `Ops.sat`.
* Simplified `buildYesHandler` and allowed it to capture a statically annotated offset.
* Introduced `buildIterYesHandler` which can capture static offet.
* Changed types of `bindSameHandler` and `bindIterSame`.
* Added `StaYesHandler` type to `Ops`.
* Renamed `updatePos` to `updatePosQ`.
* Added many methods for manipulating positions to `PosOps`.
* Made `initPos` fully static.
* Changed the type of `readChar`.
* Hid some internals of `Input`.
* Exposed some new methods for `Input`.
* Added `INPUT` to 8.6+ backend for `Defunc`.
* Added a `poke` method to `QueueLike`.
* Added a `charPred` converter to `Defunc`.

## 2.0.0.0 -- 2021-11-24

* Removed `compile`, `eval`, `codeGen` from the API.
* Removed `chainPre` and `chainPost` from the API.
* Added `Typeable` constraint to `LIFTED`.
* Removed `lamTermBool` and `userBool` from the API: `Typeable` subsumes them.
* Added `RANGES` to the `Defunc` API.

## 1.8.0.0 -- 2021-11-13

* Reversed order of arguments on `Subroutine#`, offset comes last.
* Added `Pos` type, and threaded it through
* Added `Input o` and `Input# o`, which package an `Offset o` or `Code (Rep o)` with `Pos` information.
* Added cabal flag to control the packed or unpacked representation of positions
* Added `PosSelector`
* Added `line` and `col` to primitives and `Position` to Combinator AST, as well as `SelectPos` to instructions.
* Changed `OFFSET` to `INPUT` in `Defunc`

## 1.7.2.0 -- 2021-10-31

* Added `reclaimable` to backend analysis, this allows `lookAhead` to calculate reclaim ignoring `BlockCoins`
* Fixed small bug in coin analysis that meant that `lookAhead` always contributes `0` coins (`min 0` vs `max 0`).

## 1.7.1.1 -- 2021-10-30

* Improved eta-reduction to handle multiple arguments.
* Added eta-reduction to constructed return continutations.

## 1.7.1.0 -- 2021-10-29

* Moved `parse` into core API, this will reduce the area of incompatibility.
* Added `loop` combinator.

## 1.7.0.0 -- 2021-10-28

* Added fields to the handlers to signify if they should generate a binding or not.
* Added two `Inliner` modules to handle inlining in front- and back-ends.
* Removed field from `Let` which contains the body, it was a wart.
* Refactored the internal representation of static handlers, making them more uniform.
* Added basic eta-reduction capabilities to the low-level generators: this can be improved and expanded!
* Renamed `buildIterAlways` and `buildIterSame` to `bindIterAlways` and `bindIterSame`.
* Renamed `StaHandler` to `AugmentedStaHandler`.

## 1.6.0.0 -- 2021-08-13
Fix for issue #27

* Added `BlockCoins` instruction and `CutImmune` node.
* Changed how cut compliance is determined, and stopped some incorrect factoring.
* Removed unneeded flags for analysis.

## 1.5.0.0 -- 2021-08-12
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
* Added `Common.QueueLike` to abstract both queue's common operations.
* Moved the implementation of `Queue` into a `Queue.Impl` submodule, for `RewindQueue` and testing.
* Added `GiveBursary` instruction to implement a variant of `RefundCoins`.
* Added `PrefetchChar` instruction for future prefetching on branches.
* Added `canAfford` to `Context` and removed the broken `liquidate`.
* Improved the input factoring for join points.

Misc:

* Removed the unneeded `genDefuncX` operations in `Core.Defunc`, and `ap`, hid others.
* Added type to `next` in `CharList`.
* Added auxilliary information parameter to `sat`.
* Added `fetch` and broke it out of `sat`.

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

## 1.3.0.0 -- 2021-07-03

* Improved the `Lam` reduction algorithm
* Preliminary support for `if true` reduction from `item` and `const True`
* Introduced `_if` and `ap` in `Machine.Defunc`, removed `genDefunc1`

## 1.2.0.1 -- 2021-07-03

* Added Jump-Elision optimisation to the code generator.

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

## 1.1.0.0 -- 2021-07-01

* Switched both backends to make use of `Lam` instead of `Core.Defunc`, reducing burden on GHC
* Added duplication avoidance optimisation when value to be duplicated is `Lam.Var True`

## 1.0.1.1 -- 2021-06-27

* Added input factoring to `try p <|> q` and also forms with `f <$> try p <|> q` and `try p $> x <|> q`

## 1.0.1.0 -- 2021-06-26

* Introduced `Lam` to the API and conversion functions for `Core.Defunc`
* Extra type ascriptions added to generated code

## 1.0.0.0 -- 2021-06-12

* First version. Released on an unsuspecting world.
* Core factored out of the main `parsley` package
