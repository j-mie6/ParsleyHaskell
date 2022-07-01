{-|
Module      : Parsley.Internal.Backend.Analysis
Description : Exposes various analysis passes.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the analysis passes defined within the analysis submodules. See
the extended documentation in the submodules.

@since 1.5.0.0
-}
module Parsley.Internal.Backend.Analysis (
    coinsNeeded,
    shouldInline,
    relevancy,
    reclaimable
  ) where

import Parsley.Internal.Backend.Analysis.Coins (coinsNeeded, reclaimable)
import Parsley.Internal.Backend.Analysis.Inliner (shouldInline)
import Parsley.Internal.Backend.Analysis.Relevancy (relevancy)

{- TODO
  Live Value Analysis
  -------------------

  This analysis is designed to clean up dead registers:
    * Instead of the state laws on the Combinator AST, this should catch these cases
    * By performing it here we have ready access to the control flow information
    * We'll perform global register analysis

  State Laws:
    * get *> get = get = get <* get
    * put (pure x) *> get = put (pure x) *> pure x
    * put get = pure ()
    * put x *> put (pure y) = x *> put (pure y) = put x <* put (pure y)
    -->
    * Get . Pop . Get = Get = Get . Get . Pop -- Captured by relevancy analysis
    * Get . Get = Get . Dup Subsumes the above (Dup . Pop = id, Dup . Swap = Dup)
    * px . Put . Push () . Pop . Get = px . Dup . Put . Push () . Pop -- ??? (this law is better than above)
    * Get . Put . Push () = Push () -- ??? Improved relevancy analysis?
    * px . Put . Push () . Pop . py . Put . Push () = px . Pop . Push () . Pop . py . Put . Push () = px . Put . Push () . py . Put . Push () . Pop -- Captured by dead register analysis

  Best case scenario is that we can capture all of the above optimisations
  without a need to explicitly implement them.

  Idea 1) recurse through the machine and mark branches with their liveIn set
          if a register is not liveIn after a Put instruction it can be removed
          Get r gens r
          Put r kills r
  Idea 2) recurse through the machine and collect relevancy data:
          a value on the stack is relevant if it is consumed by `Lift2` or `Case`, etc
          it is irrelevant if consumed by Pop
          if Get produces an irrelevant operand, it can be replaced by Push BOTTOM
          Dup disjoins the relevancy of the top two elements of the stack
          Swap switches the relevancy of the top two elements of the stack
  Idea 3) recurse through the machine and collect everUsed information
          if a register is never used, then the Make instruction can be removed
-}
