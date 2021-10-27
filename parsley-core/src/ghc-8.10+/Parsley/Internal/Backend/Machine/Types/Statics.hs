{-# LANGUAGE AllowAmbiguousTypes,
             MagicHash,
             TypeApplications,
             TypeFamilies #-}
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
    mkStaHandler, mkStaHandlerSta, mkStaHandlerDyn, mkStaHandlerFull,

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

import Control.Monad.ST                                (ST)
import Data.STRef                                      (STRef)
import Data.Kind                                       (Type)
import Data.Maybe                                      (fromMaybe)
import Parsley.Internal.Backend.Machine.InputRep       (Rep)
import Parsley.Internal.Backend.Machine.LetBindings    (Regs(..), Metadata, newMeta, InputCharacteristic(..))
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynCont, DynHandler, DynFunc)
import Parsley.Internal.Backend.Machine.Types.Offset   (Offset(offset), same)
import Parsley.Internal.Common.Utils                   (Code)

-- Handlers
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Handler#`
but where the static function structure has been exposed. This allows for β-reduction
on handlers, a simple form of inlining optimisation.

@since 1.4.0.0
-}
type StaHandler# s o a = Code (Rep o) -> Code (ST s (Maybe a))

mkStaHandler# :: forall o s a. DynHandler s o a -> StaHandler# s o a
mkStaHandler# dh qo# = [||$$dh $$(qo#)||]

data StaHandler s o a = StaHandler {
    staHandler# :: StaHandler# s o a,
    dynOrigin :: Maybe (DynHandler s o a)
  }

dynHandler :: (StaHandler# s o a -> DynHandler s o a) -> StaHandler s o a -> DynHandler s o a
dynHandler conv = fromMaybe . conv . staHandler# <*> dynOrigin

fromStaHandler# :: StaHandler# s o a -> StaHandler s o a
fromStaHandler# h = StaHandler h Nothing

fromDynHandler :: forall s o a. DynHandler s o a -> StaHandler s o a
fromDynHandler h = StaHandler (mkStaHandler# @o h) (Just h)

{-|
Compared with `StaHandler#`, this type allows for the encoding of various static
properties of handlers which can be carried around during the lifetime of the handlers.
This information allows the engine to optimise more aggressively, leveraging
domain-specific optimisation data.

@since 1.5.0.0
-}
data AugmentedStaHandler s o a =
  AugmentedStaHandler
    (Maybe (Offset o))     -- ^ The statically bound offset for this handler, if available.
    (StaHandlerCase s o a) -- ^ The relevant cases for the handlers behaviour

{-|
Augments a `StaHandler#` with information about what the offset is that
the handler has captured. This is a purely static handler, which is not
derived from a dynamic one.

@since 1.4.0.0
-}
mkStaHandlerSta :: Maybe (Offset o) -> StaHandler# s o a -> AugmentedStaHandler s o a
mkStaHandlerSta o = mkStaHandler o . fromStaHandler#

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynHandler` into a
`AugmentedStaHandler` taking into account the possibility that captured offset
information is available. The dynamic handler used to construct this
static handler is maintained as the origin of the handler. This means
if it is converted back the conversion is free.

@since 1.4.0.0
-}
mkStaHandlerDyn :: forall s o a. Maybe (Offset o) -> DynHandler s o a -> AugmentedStaHandler s o a
mkStaHandlerDyn c = mkStaHandler c . fromDynHandler

mkStaHandler :: Maybe (Offset o) -> StaHandler s o a -> AugmentedStaHandler s o a
mkStaHandler c = AugmentedStaHandler c . mkUnknown

{-|
When the behaviours of a handler given input that matches or does not match
its captured offset are known, this function can be used to construct a
`AugmentedStaHandler` that stores this information. This can in turn be used in
conjunction with `staHandlerEval` to statically refine the application of
a handler to its argument.

@since 1.4.0.0
-}
mkStaHandlerFull :: Offset o                   -- ^ The offset captured by the creation of the handler.
                  -> StaHandler s o a          -- ^ The full handler, which can be used when offsets are incomparable and must perform the check.
                  -> Code (ST s (Maybe a))     -- ^ The code that is executed when the captured offset matches the input.
                  -> StaHandler s o a          -- ^ The handler to be executed when offsets are known not to match.
                  -> AugmentedStaHandler s o a -- ^ A handler that carries this information around for later refinement.
mkStaHandlerFull c handler yes no = AugmentedStaHandler (Just c)
  (mkFull handler
          yes
          no)

{-|
Unlike `staHandler#`, which returns a handler that accepts @'Code' ('Rep' o)@, this
function accepts a full `Parsley.Internal.Backend.Machine.Types.Offset.Offset`,
which can be used to refine the outcome of the execution of the handler as follows:

  * If the handler has a registered captured offset, and these offsets are comparable:

      * If the offsets are equal, use the code to be executed on matching offset (See `mkStaHandlerFull`)
      * If the offsets are not equal, invoke the sub-handler, skipping the if check (see `mkStaHandlerFull`)

  * If the handler is missing a captured offset, or they are incomparable (from different sources)
     then execute the full handler, which will perform a runtime check for equivalence.

@since 1.4.0.0
-}
staHandlerEval :: AugmentedStaHandler s o a -> Offset o -> Code (ST s (Maybe a))
staHandlerEval (AugmentedStaHandler (Just c) sh) o
  | Just True <- same c o                   = maybe (staHandler# (unknown sh)) const (yesSame sh) (offset o)
  | Just False <- same c o                  = staHandler# (fromMaybe (unknown sh) (notSame sh)) (offset o)
staHandlerEval (AugmentedStaHandler _ sh) o = staHandler# (unknown sh) (offset o)

{-|
Selects the correct case out of a `StaHandlerCase` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases.

@since 1.5.0.0
-}
staHandlerCharacteristic :: AugmentedStaHandler s o a -> (StaHandler# s o a -> DynHandler s o a) -> InputCharacteristic -> StaHandler s o a
staHandlerCharacteristic (AugmentedStaHandler _ sh) conv NeverConsumes      = maybe (unknown sh) (StaHandler <$> const <*> Just . conv . const) (yesSame sh)
staHandlerCharacteristic (AugmentedStaHandler _ sh) _    (AlwaysConsumes _) = fromMaybe (unknown sh) (notSame sh)
staHandlerCharacteristic (AugmentedStaHandler _ sh) _    MayConsume         = unknown sh

staHandlerCharacteristicSta :: AugmentedStaHandler s o a -> InputCharacteristic -> StaHandler# s o a
staHandlerCharacteristicSta sh = staHandler# . staHandlerCharacteristic sh undefined

staHandlerCharacteristicDyn :: AugmentedStaHandler s o a -> (StaHandler# s o a -> DynHandler s o a) -> InputCharacteristic -> DynHandler s o a
staHandlerCharacteristicDyn sh conv = dynHandler conv . staHandlerCharacteristic sh conv

{-|
Represents potentially three handlers: one for unknown offset cases, one for offset known to be
the same, and another for offset known to be different (see `mkStaHandlerFull`). Parameterised by
a generic handler type, which is instantiated to one of `WStaHandler#` or `WDynHandler`.

@since 1.5.0.0
-}
data StaHandlerCase s (o :: Type) a = StaHandlerCase {
  -- | The static function representing this handler when offsets are incomparable.
  unknown :: StaHandler s o a,
  -- | The static value representing this handler when offsets are known to match, if available.
  yesSame :: Maybe (Code (ST s (Maybe a))),
  -- | The static function representing this handler when offsets are known not to match, if available.
  notSame :: Maybe (StaHandler s o a)
}

mkUnknown :: StaHandler s o a -> StaHandlerCase s o a
mkUnknown h = StaHandlerCase h Nothing Nothing

mkFull :: StaHandler s o a -> Code (ST s (Maybe a)) -> StaHandler s o a -> StaHandlerCase s o a
mkFull h yes no = StaHandlerCase h (Just yes) (Just no)

-- Continuations
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Cont#`
but where the static function structure has been exposed. This allows for β-reduction
on continuations, a simple form of inlining optimisation.

@since 1.4.0.0
-}
type StaCont# s o a x = Code x -> Code (Rep o) -> Code (ST s (Maybe a))

{-|
Compared with `StaCont#`, this type also bundles the static continuation
with its dynamic origin, if available.

@since 1.4.0.0
-}
data StaCont s o a x = StaCont (StaCont# s o a x) (Maybe (DynCont s o a x))

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynCont` into a
`StaCont`. The dynamic continuation used to construct this
static continuation is maintained as the origin of the continuation. This means
if it is converted back the conversion is free.

@since 1.4.0.0
-}
mkStaContDyn :: DynCont s o a x -> StaCont s o a x
mkStaContDyn dk = StaCont (\x o# -> [|| $$dk $$x $$(o#) ||]) (Just dk)

{-|
Given a static continuation, extracts the underlying continuation which
has "forgotten" any static domain-specific information it had been
attached to.

@since 1.4.0.0
-}
staCont# :: StaCont s o a x -> StaCont# s o a x
staCont# (StaCont sk _) = sk

{-|
Wraps a `StaCont#` up, under the knowledge that it is purely static and
not derived from any dynamic continuation.

@since 1.4.0.0
-}
mkStaCont :: StaCont# s o a x -> StaCont s o a x
mkStaCont sk = StaCont sk Nothing

-- Subroutines
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Subroutine#`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines, a simple form of inlining optimisation: useful for iteration.

@since 1.5.0.0
-}
type StaSubroutine# s o a x = DynCont s o a x -> Code (Rep o) -> DynHandler s o a -> Code (ST s (Maybe a))

{-|
Packages a `StaSubroutine#` along with statically determined metadata that describes it derived from
static analysis.

@since 1.5.0.0
-}
data StaSubroutine s o a x = StaSubroutine {
    -- | Extracts the underlying subroutine.
    staSubroutine# :: StaSubroutine# s o a x,
    -- | Extracts the metadata from a subroutine.
    meta :: Metadata
  }

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing the empty meta.

@since 1.5.0.0
-}
mkStaSubroutine :: StaSubroutine# s o a x -> StaSubroutine s o a x
mkStaSubroutine = mkStaSubroutineMeta newMeta

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing its metadata.

@since 1.5.0.0
-}
mkStaSubroutineMeta :: Metadata -> StaSubroutine# s o a x -> StaSubroutine s o a x
mkStaSubroutineMeta = flip StaSubroutine

{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Func`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines with registers, a simple form of inlining optimisation.

@since 1.4.0.0
-}
type family StaFunc (rs :: [Type]) s o a x where
  StaFunc '[] s o a x      = StaSubroutine s o a x
  StaFunc (r : rs) s o a x = Code (STRef s r) -> StaFunc rs s o a x

{-|
Wraps a `StaFunc` with its free registers, which are kept existential.

@since 1.4.0.0
-}
data QSubroutine s o a x = forall rs. QSubroutine (StaFunc rs s o a x) (Regs rs)

{-|
Converts a `Parsley.Internal.Backend.Machine.Types.Dynamics.DynFunc` that relies
on zero or more free registers into a `QSubroutine`, where the registers are
existentially bounds to the function.

@since 1.5.0.0
-}
qSubroutine :: forall s o a x rs. DynFunc rs s o a x -> Regs rs -> Metadata -> QSubroutine s o a x
qSubroutine func frees meta = QSubroutine (staFunc frees func) frees
  where
    staFunc :: forall rs. Regs rs -> DynFunc rs s o a x -> StaFunc rs s o a x
    staFunc NoRegs func = StaSubroutine (\dk o# dh -> [|| $$func $$dk $$(o#) $$dh ||]) meta
    staFunc (FreeReg _ witness) func = \r -> staFunc witness [|| $$func $$r ||]