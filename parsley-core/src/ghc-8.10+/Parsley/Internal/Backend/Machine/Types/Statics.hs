{-# LANGUAGE MagicHash,
             TypeFamilies #-}
module Parsley.Internal.Backend.Machine.Types.Statics (
    module Parsley.Internal.Backend.Machine.Types.Statics
  ) where

import Control.Monad.ST                                (ST)
import Data.STRef                                      (STRef)
import Data.Kind                                       (Type)
import Data.Maybe                                      (fromMaybe)
import Parsley.Internal.Backend.Machine.InputRep       (Rep)
import Parsley.Internal.Backend.Machine.LetBindings    (Regs(..))
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynCont, DynHandler, DynFunc)
import Parsley.Internal.Backend.Machine.Types.Offset   (Offset(offset), same)
import Parsley.Internal.Common.Utils                   (Code)

type StaHandler# s o a = Code (Rep o) -> Code (ST s (Maybe a))
data StaHandler s o a =
  StaHandler
    (Maybe (Offset o))                     -- ^ The statically bound offset for this handler, if available
    {-# UNPACK #-} !(StaHandlerCase s o a) -- ^ The static function representing this handler when offsets are incomparable
    (Maybe (DynHandler s o a))             -- ^ The dynamic handler that has been wrapped in this handler, if available

data StaHandlerCase s o a = StaHandlerCase {
  -- | The static function representing this handler when offsets are incomparable
  unknown :: StaHandler# s o a,
  -- | The static value representing this handler when offsets are known to match, if available
  yesSame :: Maybe (Code (ST s (Maybe a))),
  -- | The static function representing this handler when offsets are known not to match, if available
  notSame :: Maybe (StaHandler# s o a)
}

staHandler# :: StaHandler s o a -> StaHandler# s o a
staHandler# (StaHandler _ sh _) = unknown sh

staHandlerEval :: StaHandler s o a -> Offset o -> Code (ST s (Maybe a))
staHandlerEval (StaHandler (Just c) sh _) o
  | Just True <- same c o            = maybe (unknown sh) const (yesSame sh) (offset o)
  | Just False <- same c o           = fromMaybe (unknown sh) (notSame sh) (offset o)
staHandlerEval (StaHandler _ sh _) o = unknown sh (offset o)

mkStaHandler :: Offset o -> StaHandler# s o a -> StaHandler s o a
mkStaHandler o sh = StaHandler (Just o) (mkUnknown sh) Nothing

mkUnknown :: StaHandler# s o a -> StaHandlerCase s o a
mkUnknown h = StaHandlerCase h Nothing Nothing

mkFull :: StaHandler# s o a -> Code (ST s (Maybe a)) -> StaHandler# s o a -> StaHandlerCase s o a
mkFull h yes no = StaHandlerCase h (Just yes) (Just no)

staHandler :: Maybe (Offset o) -> DynHandler s o a -> StaHandler s o a
staHandler c dh = StaHandler c (mkUnknown (\o# -> [|| $$dh $$(o#) ||])) (Just dh)

staHandlerFull :: Maybe (Offset o) -> DynHandler s o a -> Code (ST s (Maybe a)) -> DynHandler s o a -> StaHandler s o a
staHandlerFull c handler yes no = StaHandler c
  (mkFull (\o# -> [|| $$handler $$(o#) ||])
          yes
          (\o# -> [|| $$no $$(o#) ||]))
  (Just handler)

staHandlerUnknown :: StaHandler# s o a -> StaHandler s o a
staHandlerUnknown h = StaHandler Nothing (mkUnknown h) Nothing

staCont :: DynCont s o a x -> StaCont s o a x
staCont dk = StaCont (\x o# -> [|| $$dk $$x $$(o#) ||]) (Just dk)

type StaCont# s o a x = Code x -> Code (Rep o) -> Code (ST s (Maybe a))
data StaCont s o a x = StaCont (StaCont# s o a x) (Maybe (DynCont s o a x))

staCont# :: StaCont s o a x -> StaCont# s o a x
staCont# (StaCont sk _) = sk

mkStaCont :: StaCont# s o a x -> StaCont s o a x
mkStaCont sk = StaCont sk Nothing

type StaSubRoutine s o a x = DynCont s o a x -> Code (Rep o) -> DynHandler s o a -> Code (ST s (Maybe a))
type family StaFunc (rs :: [Type]) s o a x where
  StaFunc '[] s o a x      = StaSubRoutine s o a x
  StaFunc (r : rs) s o a x = Code (STRef s r) -> StaFunc rs s o a x

data QSubRoutine s o a x = forall rs. QSubRoutine (StaFunc rs s o a x) (Regs rs)

qSubRoutine :: forall s o a x rs. DynFunc rs s o a x -> Regs rs -> QSubRoutine s o a x
qSubRoutine func frees = QSubRoutine (staFunc frees func) frees
  where
    staFunc :: forall rs. Regs rs -> DynFunc rs s o a x -> StaFunc rs s o a x
    staFunc NoRegs func = \dk o# dh -> [|| $$func $$dk $$(o#) $$dh ||]
    staFunc (FreeReg _ witness) func = \r -> staFunc witness [|| $$func $$r ||]