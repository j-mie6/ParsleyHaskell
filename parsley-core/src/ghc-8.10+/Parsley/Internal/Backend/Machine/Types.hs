{-|
Module      : Parsley.Internal.Backend.Machine.Types
Description : Core machine monads and re-exported internal types.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the monadic machinery used in the evaluation of a parser
machine. It also rexports parts of @Base@ and @Statics@ for compatiblity with
the ghc 8.6+ backend, which shares common code for @LetRecBuilder.hs@.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types (
    module Parsley.Internal.Backend.Machine.Types,
    -- * Compatibility Re-exports
    module Parsley.Internal.Backend.Machine.Types.Base,
    module Parsley.Internal.Backend.Machine.Types.Statics
  ) where

import Control.Monad.Reader                           (Reader, runReader)
import Control.Monad.ST                               (ST)
import Parsley.Internal.Backend.Machine.Types.Base    (Func)
import Parsley.Internal.Backend.Machine.Types.Context (Ctx)
import Parsley.Internal.Backend.Machine.Types.State   (Γ)
import Parsley.Internal.Backend.Machine.Types.Statics (QSubroutine, qSubroutine)
import Parsley.Internal.Common.Utils                  (Code)
import Parsley.Internal.Core.Result                   (Result)

{-|
The monad stack used to evaluate a parser machine, see `run`.

@since 1.4.0.0
-}
type MachineMonad s o err a xs n m r = Reader (Ctx s o err a) (Γ s o err a xs n m r -> Code (ST s (Result err a)))

{-|
Wraps up the `MachineMonad` type so that it can serve as the carrier of `Parsley.Internal.Common.Indexed.cata4`.

@since 1.4.0.0
-}
newtype Machine s o err a xs n m r = Machine { getMachine :: MachineMonad s o err a xs n m r }

{-|
Used to execute the evaluator for a parser machine, resulting in the final code
to be returned back to the User API.

@since 1.4.0.0
-}
run :: Machine s o err a xs n m r   -- ^ The action that will generate the final code.
    -> Γ s o err a xs n m r         -- ^ The informaton that is threaded through the parsing machinery, which appears in some form in the generated code.
    -> Ctx s o err a              -- ^ Static information used in the code generation process, but not in the generated code.
    -> Code (ST s (Result err a)) -- ^ The code that represents this parser (after having been given an input).
run = flip . runReader . getMachine
