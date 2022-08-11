{-# LANGUAGE AllowAmbiguousTypes,
             MagicHash,
             RecordWildCards,
             TypeApplications,
             TypeFamilies,
             UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Statics
Description : Representation of components that exist within a statically known component
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the types that represent statically known information that can be
refined and manipulated within a single compilation unit: i.e. not crossing recursion or
call boundaries.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Statics (
    -- * Handlers
    StaHandler#, StaHandler, AugmentedStaHandler, StaHandlerCase,

    -- ** @StaHandler@ Operations
    fromStaHandler#, fromDynHandler, staHandler#,

    -- ** @AugmentedStaHandler@ Builders
    -- | The following functions are builders of `AugmentedStaHandler`.
    augmentHandler, augmentHandlerSta, augmentHandlerDyn, augmentHandlerFull,

    -- ** @AugmentedStaHandler@ Interpreters
    -- | The following functions interpret or extract information from `StaHandler`.
    staHandlerEval, staHandlerCharacteristicSta, staHandlerCharacteristicDyn,

    -- * Return Continuations
    StaCont#, StaCont(..),
    mkStaCont, mkStaContDyn,
    staCont#,

    -- * Subroutines
    QSubroutine(..), StaSubroutine, StaSubroutine#, StaFunc,
    -- ** Subroutine Builders
    qSubroutine, mkStaSubroutine, mkStaSubroutineMeta,

    -- ** Subroutine Extractors
    staSubroutine#, meta,
  ) where

import Control.Monad.ST                                           (ST)
import Data.STRef                                                 (STRef)
import Data.Kind                                                  (Type)
import Data.Maybe                                                 (fromMaybe)
import Parsley.Internal.Backend.Machine.LetBindings               (Regs(..), Metadata, newMeta)
import Parsley.Internal.Backend.Machine.Types.Dynamics            (DynCont, DynHandler, DynFunc)
import Parsley.Internal.Backend.Machine.Types.Errors.Defunc       (DefuncError{-, DefuncGhosts-})
import Parsley.Internal.Backend.Machine.Types.Input               (Input(..), Input#(..), fromInput)
import Parsley.Internal.Backend.Machine.Types.Input.Offset        (Offset, same)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic(..))
import Parsley.Internal.Common.Utils                              (Code)
import Parsley.Internal.Core.Result                               (Result)

-- Handlers
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Handler#`
but where the static function structure has been exposed. This allows for β-reduction
on handlers, a simple form of inlining optimisation.

@since 1.8.0.0
-}
type StaHandler# s o err a = Input# o -> Code DefuncError -> Code (ST s (Result err a))

mkStaHandler# :: forall o s err a. DynHandler s o err a -> StaHandler# s o err a
mkStaHandler# dh inp err = [||$$dh $$(pos# inp) $$(off# inp) $$err||]

{-|
Encapsulates a static handler with its possible dynamic origin for costless conversion.

@since 1.7.0.0
-}
data StaHandler s o err a = StaHandler {
    {-|
    Extracts the raw static component out of a static handler.

    @since 1.7.0.0
    -}
    staHandler# :: StaHandler# s o err a,
    dynOrigin :: Maybe (DynHandler s o err a)
  }

dynHandler :: (StaHandler# s o err a -> DynHandler s o err a) -> StaHandler s o err a -> DynHandler s o err a
dynHandler conv = fromMaybe . conv . staHandler# <*> dynOrigin

{-|
Builds a `StaHandler` out of a `StaHandler#`, assumed to have no dynamic component.

@since 1.7.0.0
-}
fromStaHandler# :: StaHandler# s o err a -> StaHandler s o err a
fromStaHandler# h = StaHandler h Nothing

{-|
Builds a `StaHandler` out of a `DynHandler`, which is converted in the process.

@since 1.7.0.0
-}
fromDynHandler :: forall s o err a. DynHandler s o err a -> StaHandler s o err a
fromDynHandler h = StaHandler (mkStaHandler# @o h) (Just h)

{-|
Compared with `StaHandler#`, this type allows for the encoding of various static
properties of handlers which can be carried around during the lifetime of the handlers.
This information allows the engine to optimise more aggressively, leveraging
domain-specific optimisation data.

@since 1.7.0.0
-}
data AugmentedStaHandler s o err a =
  AugmentedStaHandler
    (Maybe (Offset o))         -- ^ The statically bound offset for this handler, if available.
    (StaHandlerCase s o err a) -- ^ The relevant cases for the handlers behaviour

{-|
Augments a `StaHandler#` with information about what the offset is that
the handler has captured. This is a purely static handler, which is not
derived from a dynamic one.

@since 1.8.0.0
-}
augmentHandlerSta :: Maybe (Input o) -> StaHandler# s o err a -> AugmentedStaHandler s o err a
augmentHandlerSta o = augmentHandler o . fromStaHandler#

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynHandler` into a
`AugmentedStaHandler` taking into account the possibility that captured offset
information is available. The dynamic handler used to construct this
static handler is maintained as the origin of the handler. This means
if it is converted back the conversion is free.

@since 1.7.0.0
-}
augmentHandlerDyn :: forall s o err a. Maybe (Input o) -> DynHandler s o err a -> AugmentedStaHandler s o err a
augmentHandlerDyn c = augmentHandler c . fromDynHandler

{-|
Augments a static handler with information about its captured offset.

@since 1.7.0.0
-}
augmentHandler :: Maybe (Input o) -> StaHandler s o err a -> AugmentedStaHandler s o err a
augmentHandler c = AugmentedStaHandler (fmap off c) . mkUnknown

{-|
When the behaviours of a handler given input that matches or does not match
its captured offset are known, this function can be used to construct a
`AugmentedStaHandler` that stores this information. This can in turn be used in
conjunction with `staHandlerEval` to statically refine the application of
a handler to its argument.

@since 1.7.0.0
-}
augmentHandlerFull :: Input o                       -- ^ The offset captured by the creation of the handler.
                   -> StaHandler s o err a          -- ^ The full handler, which can be used when offsets are incomparable and must perform the check.
                   -> (Code DefuncError -> Code (ST s (Result err a)))    -- ^ The code that is executed when the captured offset matches the input.
                   -> StaHandler s o err a          -- ^ The handler to be executed when offsets are known not to match.
                   -> AugmentedStaHandler s o err a -- ^ A handler that carries this information around for later refinement.
augmentHandlerFull c handler yes no = AugmentedStaHandler (Just (off c))
  (mkFull handler
          yes
          no)

{-|
Unlike `staHandler#`, which returns a handler that accepts @'Input' o@, this
function accepts a full `Parsley.Internal.Backend.Machine.Types.Offset.Offset`,
which can be used to refine the outcome of the execution of the handler as follows:

  * If the handler has a registered captured offset, and these offsets are comparable:

      * If the offsets are equal, use the code to be executed on matching offset (See `augmentHandlerFull`)
      * If the offsets are not equal, invoke the sub-handler, skipping the if check (see `augmentHandlerFull`)

  * If the handler is missing a captured offset, or they are incomparable (from different sources)
     then execute the full handler, which will perform a runtime check for equivalence.

@since 1.7.0.0
-}
staHandlerEval :: AugmentedStaHandler s o err a -> Input o -> Code DefuncError -> Code (ST s (Result err a))
staHandlerEval (AugmentedStaHandler (Just c) sh) inp
  | Just True <- same c (off inp)             = maybe (staHandler# (unknown sh)) const (yesSame sh) (fromInput inp)
  | Just False <- same c (off inp)            = staHandler# (fromMaybe (unknown sh) (notSame sh)) (fromInput inp)
staHandlerEval (AugmentedStaHandler _ sh) inp = staHandler# (unknown sh) (fromInput inp)

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases.

@since 1.7.0.0
-}
staHandlerCharacteristic :: AugmentedStaHandler s o err a -> (StaHandler# s o err a -> DynHandler s o err a) -> InputCharacteristic -> StaHandler s o err a
staHandlerCharacteristic (AugmentedStaHandler _ sh) conv NeverConsumes      = maybe (unknown sh) (StaHandler <$> const <*> Just . conv . const) (yesSame sh)
staHandlerCharacteristic (AugmentedStaHandler _ sh) _    (AlwaysConsumes _) = fromMaybe (unknown sh) (notSame sh)
staHandlerCharacteristic (AugmentedStaHandler _ sh) _    MayConsume         = unknown sh

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases. Extracts the
static handler out of the result.

@since 1.7.0.0
-}
staHandlerCharacteristicSta :: AugmentedStaHandler s o err a -> InputCharacteristic -> StaHandler# s o err a
staHandlerCharacteristicSta sh = staHandler# . staHandlerCharacteristic sh undefined

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases. Extracts a
dynamic result out of the static handler given a conversion function.

@since 1.7.0.0
-}
staHandlerCharacteristicDyn :: AugmentedStaHandler s o err a -> (StaHandler# s o err a -> DynHandler s o err a) -> InputCharacteristic -> DynHandler s o err a
staHandlerCharacteristicDyn sh conv = dynHandler conv . staHandlerCharacteristic sh conv

{-|
Represents potentially three handlers: one for unknown offset cases, one for offset known to be
the same, and another for offset known to be different (see `augmentHandlerFull`).

@since 1.7.0.0
-}
data StaHandlerCase s (o :: Type) err a = StaHandlerCase {
  -- | The static function representing this handler when offsets are incomparable.
  unknown :: StaHandler s o err a,
  -- | The static value representing this handler when offsets are known to match, if available.
  yesSame :: Maybe (Code DefuncError -> Code (ST s (Result err a))),
  -- | The static function representing this handler when offsets are known not to match, if available.
  notSame :: Maybe (StaHandler s o err a)
}

mkUnknown :: StaHandler s o err a -> StaHandlerCase s o err a
mkUnknown h = StaHandlerCase h Nothing Nothing

mkFull :: StaHandler s o err a -> (Code DefuncError -> Code (ST s (Result err a))) -> StaHandler s o err a -> StaHandlerCase s o err a
mkFull h yes no = StaHandlerCase h (Just yes) (Just no)

-- Continuations
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Cont#`
but where the static function structure has been exposed. This allows for β-reduction
on continuations, a simple form of inlining optimisation.

@since 1.8.0.0
-}
type StaCont# s o err a x = Code x -> Input# o -> Code (ST s (Result err a))

{-|
Compared with `StaCont#`, this type also bundles the static continuation
with its dynamic origin, if available.

@since 1.4.0.0
-}
data StaCont s o err a x = StaCont (StaCont# s o err a x) (Maybe (DynCont s o err a x))

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynCont` into a
`StaCont`. The dynamic continuation used to construct this
static continuation is maintained as the origin of the continuation. This means
if it is converted back the conversion is free.

@since 1.4.0.0
-}
mkStaContDyn :: DynCont s o err a x -> StaCont s o err a x
mkStaContDyn dk = StaCont (\x inp -> [|| $$dk $$x $$(pos# inp) $$(off# inp) ||]) (Just dk)

{-|
Given a static continuation, extracts the underlying continuation which
has "forgotten" any static domain-specific information it had been
attached to.

@since 1.4.0.0
-}
staCont# :: StaCont s o err a x -> StaCont# s o err a x
staCont# (StaCont sk _) = sk

{-|
Wraps a `StaCont#` up, under the knowledge that it is purely static and
not derived from any dynamic continuation.

@since 1.4.0.0
-}
mkStaCont :: StaCont# s o err a x -> StaCont s o err a x
mkStaCont sk = StaCont sk Nothing

-- Subroutines
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Subroutine#`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines, a simple form of inlining optimisation: useful for iteration.

@since 1.8.0.0
-}
type StaSubroutine# s o err a x = DynCont s o err a x -> DynHandler s o err a -> Input# o -> Code (ST s (Result err a))

{-|
Packages a `StaSubroutine#` along with statically determined metadata that describes it derived from
static analysis.

@since 1.5.0.0
-}
data StaSubroutine s o err a x = StaSubroutine {
    -- | Extracts the underlying subroutine.
    staSubroutine# :: StaSubroutine# s o err a x,
    -- | Extracts the metadata from a subroutine.
    meta :: Metadata
  }

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing the empty meta.

@since 1.5.0.0
-}
mkStaSubroutine :: StaSubroutine# s o err a x -> StaSubroutine s o err a x
mkStaSubroutine = mkStaSubroutineMeta newMeta

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing its metadata.

@since 1.5.0.0
-}
mkStaSubroutineMeta :: Metadata -> StaSubroutine# s o err a x -> StaSubroutine s o err a x
mkStaSubroutineMeta = flip StaSubroutine

{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Func`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines with registers, a simple form of inlining optimisation.

@since 1.4.0.0
-}
type family StaFunc (rs :: [Type]) s o err a x where
  StaFunc '[] s o err a x      = StaSubroutine s o err a x
  StaFunc (r : rs) s o err a x = Code (STRef s r) -> StaFunc rs s o err a x

{-|
Wraps a `StaFunc` with its free registers, which are kept existential.

@since 1.4.0.0
-}
data QSubroutine s o err a x = forall rs. QSubroutine (StaFunc rs s o err a x) (Regs rs)

{-|
Converts a `Parsley.Internal.Backend.Machine.Types.Dynamics.DynFunc` that relies
on zero or more free registers into a `QSubroutine`, where the registers are
existentially bounds to the function.

@since 1.5.0.0
-}
qSubroutine :: forall s o err a x rs. DynFunc rs s o err a x -> Regs rs -> Metadata -> QSubroutine s o err a x
qSubroutine func frees meta = QSubroutine (staFunc frees func) frees
  where
    staFunc :: forall rs. Regs rs -> DynFunc rs s o err a x -> StaFunc rs s o err a x
    staFunc NoRegs func = StaSubroutine (\dk dh inp -> [|| $$func $$dk $$dh $$(pos# inp) $$(off# inp) ||]) meta
    staFunc (FreeReg _ witness) func = \r -> staFunc witness [|| $$func $$r ||]
