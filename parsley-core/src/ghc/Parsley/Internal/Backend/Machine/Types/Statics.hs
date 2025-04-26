{-# LANGUAGE AllowAmbiguousTypes,
             ImplicitParams,
             MagicHash,
             RecordWildCards,
             TypeApplications,
             TypeFamilies,
             ScopedTypeVariables,
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
    -- * Register stacks
    StaRegisterStack#, toDynRegStack, 
    -- * Handlers
    StaHandler#, StaHandler(..), AugmentedStaHandler, QAugmentedStaHandler(..), StaHandlerCase, StaSameHandler,

    -- ** @StaHandler@ Operations
    fromStaHandler#, fromDynHandler, staHandler#, SomeCallableSubroutine(..),

    -- ** @AugmentedStaHandler@ Builders
    -- | The following functions are builders of `AugmentedStaHandler`.
    augmentHandler, augmentHandlerSta, augmentHandlerDyn, augmentHandlerFull,

    -- ** @AugmentedStaHandler@ Interpreters
    -- | The following functions interpret or extract information from `StaHandler`.
    staHandlerEval, staHandlerCharacteristicSta, staHandlerCharacteristicDyn,

    -- * Return Continuations
    StaCont#, StaCont(..), QStaCont(..),
    mkStaCont, mkStaContDyn,
    staCont#,

    -- * Subroutines
    QSubroutine(..), QLooproutine(..), StaSubroutine, StaSubroutine#, StaFunc,
    -- ** Subroutine Builders
    qSubroutine, mkStaSubroutine, mkStaSubroutineMeta,

    -- ** Subroutine Extractors
    staSubroutine#, meta,
  ) where

import Control.Monad.ST                                           (ST)
import Data.STRef                                                 (STRef)
import Data.Kind                                                  (Type)
import Data.Maybe                                                 (fromMaybe)
import Parsley.Internal.Backend.Machine.LetBindings               (Metadata, newMeta)
import Parsley.Internal.Backend.Machine.InputOps                  (DynOps)
import Parsley.Internal.Backend.Machine.Types.Registers           (Regs(..), RegBindNames(..))
import Parsley.Internal.Backend.Machine.Types.Dynamics            (DynCont, DynHandler, DynFunc, DynRegisterStack)
import Parsley.Internal.Backend.Machine.Types.Input               (Input(..), Input#(..), fromInput)
import Parsley.Internal.Backend.Machine.Types.Input.Offset        (Offset, same)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic(..))
import Parsley.Internal.Common.Utils                              (Code)

import qualified Parsley.Internal.Opt as Opt

-- Register Stack 
type family StaRegisterStack# (rs :: [Type]) x where 
  StaRegisterStack# '[] x      = Code x
  StaRegisterStack# (r : rs) x = Code r -> StaRegisterStack# rs x

fromDynRegStack :: forall rs x. DynRegisterStack rs x -> Regs rs -> StaRegisterStack# rs x
fromDynRegStack drs NoRegs      = drs
fromDynRegStack drs (Regs _ rs) = \r -> fromDynRegStack @_ @x [|| $$drs $$r ||] rs  

toDynRegStack :: forall rs x. Regs rs ->  StaRegisterStack# rs x -> DynRegisterStack rs x
toDynRegStack NoRegs f = f 
toDynRegStack (Regs _ rs) f = [|| \r -> $$(toDynRegStack @_ @x rs (f [|| r ||])) ||]

-- Handlers
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Handler#`
but where the static function structure has been exposed. This allows for β-reduction
on handlers, a simple form of inlining optimisation.

@since 1.8.0.0
-}
type family StaHandler# (hs :: [Type]) s o a where
    StaHandler# '[] s o a = Input# o -> Code (ST s (Maybe a))
    StaHandler# (h:hs) s o a = Code h -> StaHandler# hs s o a

mkStaHandler# :: forall hs o s a. Regs hs -> DynHandler hs s o a -> StaHandler# hs s o a
mkStaHandler# = mkSta
  where
    mkSta :: forall hs. Regs hs -> DynHandler hs s o a -> StaHandler# hs s o a
    mkSta NoRegs dh = \inp -> [||$$dh $$(pos# inp) $$(off# inp)||]
    mkSta (Regs _ rs) dh = \r -> mkSta rs [||$$dh $$r ||]


{-|
Encapsulates a static handler with its possible dynamic origin for costless conversion.

@since 1.7.0.0
-}
data StaHandler hs s o a = StaHandler {
    {-|
    Extracts the raw static component out of a static handler.

    @since 1.7.0.0
    -}
    staHandler# :: !(StaHandler# hs s o a),
    dynOrigin :: !(Maybe (DynHandler hs s o a))
  }

dynHandler :: (StaHandler# hs s o a -> DynHandler hs s o a) -> StaHandler hs s o a -> DynHandler hs s o a
dynHandler conv = fromMaybe . conv . staHandler# <*> dynOrigin

{-|
Builds a `StaHandler` out of a `StaHandler#`, assumed to have no dynamic component.

@since 1.7.0.0
-}
fromStaHandler# :: StaHandler# hs s o a -> StaHandler hs s o a
fromStaHandler# h = StaHandler h Nothing

{-|
Builds a `StaHandler` out of a `DynHandler`, which is converted in the process.

@since 1.7.0.0
-}
fromDynHandler :: forall hs s o a. Regs hs -> DynHandler hs s o a -> StaHandler hs s o a
fromDynHandler regs h = StaHandler (mkStaHandler# @hs @o @s @a regs h) (Just h)

{-|
Compared with `StaHandler#`, this type allows for the encoding of various static
properties of handlers which can be carried around during the lifetime of the handlers.
This information allows the engine to optimise more aggressively, leveraging
domain-specific optimisation data.

@since 1.7.0.0
-}
data AugmentedStaHandler hs s o a =
  AugmentedStaHandler
    (Maybe (Offset o))        -- ^ The statically bound offset for this handler, if available.
    (StaHandlerCase hs s o a) -- ^ The relevant cases for the handlers behaviour

{-| 
Wrapper for `AugmentedStaHandler` to wrap away the input registers in an existential and package witnesses alongside them
-}
data QAugmentedStaHandler s o a = forall hs. QAugmentedStaHandler !(AugmentedStaHandler hs s o a) !(Regs hs)

{-|
Augments a `StaHandler#` with information about what the offset is that
the handler has captured. This is a purely static handler, which is not
derived from a dynamic one.

@since 1.8.0.0
-}
augmentHandlerSta :: Maybe (Input o) -> StaHandler# hs s o a -> AugmentedStaHandler hs s o a
augmentHandlerSta o = augmentHandler o . fromStaHandler#

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynHandler` into a
`AugmentedStaHandler` taking into account the possibility that captured offset
information is available. The dynamic handler used to construct this
static handler is maintained as the origin of the handler. This means
if it is converted back the conversion is free.

@since 1.7.0.0
-}
augmentHandlerDyn :: forall hs s o a. Maybe (Input o) ->  DynHandler hs s o a -> Regs hs -> AugmentedStaHandler hs s o a
augmentHandlerDyn c dh regs = augmentHandler c $ fromDynHandler regs dh

{-|
Augments a static handler with information about its captured offset.

@since 1.7.0.0
-}
augmentHandler :: Maybe (Input o) -> StaHandler hs s o a -> AugmentedStaHandler hs s o a
augmentHandler c = AugmentedStaHandler (fmap off c) . mkUnknown

{-|
When the behaviours of a handler given input that matches or does not match
its captured offset are known, this function can be used to construct a
`AugmentedStaHandler` that stores this information. This can in turn be used in
conjunction with `staHandlerEval` to statically refine the application of
a handler to its argument.

@since 1.7.0.0
-}
augmentHandlerFull :: Input o                      -- ^ The offset captured by the creation of the handler.
                   -> StaHandler hs s o a          -- ^ The full handler, which can be used when offsets are incomparable and must perform the check.
                   -> StaSameHandler hs s a        -- ^ The code that is executed when the captured offset matches the input.
                   -> StaHandler hs s o a          -- ^ The handler to be executed when offsets are known not to match.
                   -> AugmentedStaHandler hs s o a -- ^ A handler that carries this information around for later refinement.
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
staHandlerEval :: (DynOps o, ?flags :: Opt.Flags) => AugmentedStaHandler hs s o a -> RegBindNames hs -> Input o -> Code (ST s (Maybe a))
staHandlerEval (AugmentedStaHandler (Just c) sh) regs inp
  | Opt.deduceFailPath ?flags
  , Just True <- same c (off inp)             = maybe (injectStaHandlerRegs regs $ staHandler# (unknown sh)) (const . injectStaSameHandlerRegs regs) (yesSame sh) (fromInput inp)
  | Opt.deduceFailPath ?flags
  , Just False <- same c (off inp)            = (injectStaHandlerRegs regs . staHandler#) (fromMaybe (unknown sh) (notSame sh)) (fromInput inp)
staHandlerEval (AugmentedStaHandler _ sh) regs inp = (injectStaHandlerRegs regs $ staHandler# (unknown sh)) (fromInput inp)

injectStaHandlerRegs :: forall hs s o a. RegBindNames hs -> StaHandler# hs s o a -> StaHandler# '[] s o a
injectStaHandlerRegs NoName h = h
injectStaHandlerRegs (RegName _ name rs) h = injectStaHandlerRegs @_ @_ @o rs (h name)

injectStaSameHandlerRegs :: forall hs s a. RegBindNames hs -> StaSameHandler hs s a -> Code (ST s (Maybe a))
injectStaSameHandlerRegs NoName h = h
injectStaSameHandlerRegs (RegName _ name rs) h = injectStaSameHandlerRegs rs (h name)

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases.

@since 1.7.0.0
-}
staHandlerCharacteristic :: forall hs s o a. Regs hs -> AugmentedStaHandler hs s o a -> (StaHandler# hs s o a -> DynHandler hs s o a) -> InputCharacteristic -> StaHandler hs s o a
staHandlerCharacteristic regs (AugmentedStaHandler _ sh) conv NeverConsumes      = maybe (unknown sh) (StaHandler <$> sameToSta regs <*> Just . conv . sameToSta regs) (yesSame sh)
  where
      sameToSta :: forall hs. Regs hs -> StaSameHandler hs s a -> StaHandler# hs s o a
      sameToSta NoRegs      h = const h
      sameToSta (Regs _ rs) h = sameToSta rs . h
staHandlerCharacteristic _ (AugmentedStaHandler _ sh) _    (AlwaysConsumes _) = fromMaybe (unknown sh) (notSame sh)
staHandlerCharacteristic _ (AugmentedStaHandler _ sh) _    MayConsume         = unknown sh

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases. Extracts the
static handler out of the result.

@since 1.7.0.0
-}
staHandlerCharacteristicSta :: Regs hs -> AugmentedStaHandler hs s o a -> InputCharacteristic -> StaHandler# hs s o a
staHandlerCharacteristicSta regs sh = staHandler# . staHandlerCharacteristic regs sh undefined

{-|
Selects the correct case out of a `AugmentedStaHandler` depending on what the `InputCharacteristic` that
governs the use of the handler is. This means that it can select any of the three cases. Extracts a
dynamic result out of the static handler given a conversion function.

@since 1.7.0.0
-}
staHandlerCharacteristicDyn :: Regs hs -> AugmentedStaHandler hs s o a -> (StaHandler# hs s o a -> DynHandler hs s o a) -> InputCharacteristic -> DynHandler hs s o a
staHandlerCharacteristicDyn regs sh conv = dynHandler conv . staHandlerCharacteristic regs sh conv

{-|
Type family to encapsulate a n-ary handler which knows that offsets match.
-}
type family StaSameHandler (hs :: [Type]) s a where
  StaSameHandler '[] s a = Code (ST s (Maybe a))
  StaSameHandler (h:hs) s a = Code h -> StaSameHandler hs s a

{-|
Represents potentially three handlers: one for unknown offset cases, one for offset known to be
the same, and another for offset known to be different (see `augmentHandlerFull`).

@since 1.7.0.0
-}
data StaHandlerCase hs s (o :: Type) a = StaHandlerCase {
  -- | The static function representing this handler when offsets are incomparable.
  unknown :: {-# UNPACK #-} !(StaHandler hs s o a),
  -- | The static value representing this handler when offsets are known to match, if available.
  yesSame :: !(Maybe (StaSameHandler hs s a)),
  -- | The static function representing this handler when offsets are known not to match, if available.
  notSame :: !(Maybe (StaHandler hs s o a))
}

mkUnknown :: StaHandler hs s o a -> StaHandlerCase hs s o a
mkUnknown h = StaHandlerCase h Nothing Nothing

mkFull :: StaHandler hs s o a -> StaSameHandler hs s a -> StaHandler hs s o a -> StaHandlerCase hs s o a
mkFull h yes no = StaHandlerCase h (Just yes) (Just no)

-- Continuations
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Cont#`
but where the static function structure has been exposed. This allows for β-reduction
on continuations, a simple form of inlining optimisation.

@since 1.8.0.0
-}
type StaCont# (rs :: [Type]) s o a x = Code x -> Input# o -> StaRegisterStack# rs (ST s (Maybe a))

{-|
Compared with `StaCont#`, this type also bundles the static continuation
with its dynamic origin, if available.

@since 1.4.0.0
-}
-- leave this lazy or it'll expode
data StaCont rs s o a x = StaCont (StaCont# rs s o a x) !(Maybe (DynCont rs s o a x))

{-|
`StaCont` where the registers are hidden behind an existential.
-}
data QStaCont s o a x = forall rs. QStaCont (StaCont rs s o a x) (Regs rs)

{-|
Converts a `Parsley.Internal.Machine.Types.Dynamics.DynCont` into a
`StaCont`. The dynamic continuation used to construct this
static continuation is maintained as the origin of the continuation. This means
if it is converted back the conversion is free.

@since 1.4.0.0
-}
mkStaContDyn :: forall rs o s a x. DynCont rs s o a x -> Regs rs -> StaCont rs s o a x
mkStaContDyn dk regs = StaCont (\x inp -> fromDynRegStack @_ @(ST s (Maybe a)) [|| $$dk $$x $$(pos# inp) $$(off# inp) ||] regs) (Just dk)


{-|
Given a static continuation, extracts the underlying continuation which
has "forgotten" any static domain-specific information it had been
attached to.

@since 1.4.0.0
-}
staCont# :: StaCont xs s o a x -> StaCont# xs s o a x
staCont# (StaCont sk _) = sk

{-|
Wraps a `StaCont#` up, under the knowledge that it is purely static and
not derived from any dynamic continuation.

@since 1.4.0.0
-}
mkStaCont :: StaCont# xs s o a x -> StaCont xs s o a x
mkStaCont sk = StaCont sk Nothing

-- Subroutines
{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Subroutine#`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines, a simple form of inlining optimisation: useful for iteration.

NB: made into a type family to allow n-arity

@since 1.8.0.0
-}
type family StaSubroutine# (xs :: [Type]) (hs :: [Type]) (ys :: [Type]) s o a y where
  StaSubroutine# '[] hs ys s o a y      = DynCont ys s o a y -> DynHandler hs s o a -> Input# o -> Code (ST s (Maybe a))
  StaSubroutine# (x : xs) hs ys s o a y = Code x -> StaSubroutine# xs hs ys s o a y

{-|
Packages a `StaSubroutine#` along with statically determined metadata that describes it derived from
static analysis.

@since 1.5.0.0
-}
data StaSubroutine (xs :: [Type]) (hs :: [Type]) (ys :: [Type]) s o a x = StaSubroutine {
    -- | Extracts the underlying subroutine.
    staSubroutine# :: !(StaSubroutine# xs hs ys s o a x),
    -- | Extracts the metadata from a subroutine.
    meta :: {-# UNPACK #-} !Metadata
  }

{-| 
Subroutine that has been supplied all it's input registers. 
-}
data SomeCallableSubroutine s o a x = forall hs ys. SomeCallableSubroutine (StaSubroutine '[] hs ys s o a x) !(Regs hs) !(Regs ys)

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing the empty meta.

@since 1.5.0.0
-}
mkStaSubroutine :: StaSubroutine# xs hs ys s o a x -> StaSubroutine xs hs ys s o a x
mkStaSubroutine = mkStaSubroutineMeta newMeta

{-|
Converts a `StaSubroutine#` into a `StaSubroutine` by providing its metadata.

@since 1.5.0.0
-}
mkStaSubroutineMeta :: forall xs hs ys s o a x. Metadata -> StaSubroutine# xs hs ys s o a x -> StaSubroutine xs hs ys s o a x
mkStaSubroutineMeta = flip StaSubroutine

{-|
This represents the translation of `Parsley.Internal.Backend.Machine.Types.Base.Func`
but where the static function structure has been exposed. This allows for β-reduction
on subroutines with registers, a simple form of inlining optimisation.

@since 1.4.0.0
-}
type StaFunc rs hs ys s o a x = StaSubroutine rs hs ys s o a x


{-|
Wraps a `StaFunc` with its free registers, which are kept existential.

@since 1.4.0.0
-}
data QSubroutine s o a x = forall rs hs ys. QSubroutine !(StaFunc rs hs ys s o a x) !(Regs rs) !(Regs hs) !(Regs ys)

{-|
Wraps a `StaSubroutine` with its free registers, handler registers, and return continuation registers are kept existential.

-}
data QLooproutine s o a x = forall xs hs ys. QLooproutine !(StaSubroutine xs hs ys s o a x) !(Regs xs) !(Regs hs) !(Regs ys)

{-|
Converts a `Parsley.Internal.Backend.Machine.Types.Dynamics.DynFunc` that relies
on zero or more free registers into a `QSubroutine`, where the registers are
existentially bounds to the function.

@since 1.5.0.0
-}
qSubroutine :: forall s o a x rs hs ys. DynFunc rs hs ys s o a x -> Regs rs -> Regs hs -> Regs ys -> Metadata -> QSubroutine s o a x
qSubroutine func frees handlerFrees retFrees meta = QSubroutine (StaSubroutine (staFunc frees func) meta) frees handlerFrees retFrees
  where
    staFunc :: forall rs. Regs rs -> DynFunc rs hs ys s o a x -> StaSubroutine# rs hs ys s o a x
    staFunc NoRegs func = \dk dh inp -> [|| $$func $$dk $$dh $$(pos# inp) $$(off# inp) ||]
    staFunc (Regs _ witness) func = \r -> staFunc witness [|| $$func $$r ||]
