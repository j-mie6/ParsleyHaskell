{-# LANGUAGE StandaloneKindSignatures, TypeApplications #-}
module Parsley.Internal.Backend.Machine.Defunc (module Parsley.Internal.Backend.Machine.Defunc) where

import Data.Proxy                                (Proxy(Proxy))
import Parsley.Internal.Backend.Machine.InputOps (PositionOps(same))
import Parsley.Internal.Backend.Machine.InputRep (Rep)
import Parsley.Internal.Common.Utils             (Code, WQ(WQ))

import qualified Parsley.Internal.Core.Defunc as Core (Defunc(BLACK), ap, genDefunc, genDefunc1, genDefunc2)

data Defunc a where
  USER    :: Core.Defunc a -> Defunc a
  BOTTOM  :: Defunc a
  SAME    :: PositionOps o => Defunc (o -> o -> Bool)
  FREEVAR :: Code a -> Defunc a
  OFFSET  :: Code (Rep o) -> Defunc o

ap2 :: Defunc (a -> b -> c) -> Defunc a -> Defunc b -> Defunc c
ap2 f@SAME (OFFSET o1) (OFFSET o2) = USER (black (apSame f o1 o2))
  where
    apSame :: forall o. Defunc (o -> o -> Bool) -> Code (Rep o) -> Code (Rep o) -> Code Bool
    apSame SAME = same (Proxy @o)
    apSame _    = undefined
ap2 f x y = USER (Core.ap (Core.ap (seal f) (seal x)) (seal y))
  where
    seal :: Defunc a -> Core.Defunc a
    seal (USER x) = x
    seal x        = black (genDefunc x)

black :: Code a -> Core.Defunc a
black = Core.BLACK . WQ undefined

genDefunc :: Defunc a -> Code a
genDefunc (USER x)    = Core.genDefunc x
genDefunc BOTTOM      = [||undefined||]
genDefunc (FREEVAR x) = x
genDefunc SAME        = error "Cannot materialise the same function in the regular way"
genDefunc (OFFSET _)  = error "Cannot materialise an unboxed offset in the regular way"

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 (USER f) qx = Core.genDefunc1 f qx
genDefunc1 f qx        = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 (USER f) qx qy = Core.genDefunc2 f qx qy
genDefunc2 f qx qy        = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a) where
  show (USER x) = show x
  show SAME = "same"
  show BOTTOM = "[[irrelevant]]"
  show (FREEVAR _) = "x"
  show (OFFSET _)  = "an offset"