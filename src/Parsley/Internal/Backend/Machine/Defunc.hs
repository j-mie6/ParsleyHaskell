module Parsley.Internal.Backend.Machine.Defunc (module Parsley.Internal.Backend.Machine.Defunc) where

import Parsley.Internal.Backend.Machine.InputOps (PositionOps(same))
import Parsley.Internal.Common.Utils             (Code)

import qualified Parsley.Internal.Core.Defunc as Core (Defunc, genDefunc, genDefunc1, genDefunc2)

data Defunc a where
  USER   :: Core.Defunc a -> Defunc a
  BOTTOM :: Defunc a
  SAME   :: PositionOps o => Defunc (o -> o -> Bool)

genDefunc :: Defunc a -> Code a
genDefunc (USER x) = Core.genDefunc x
genDefunc BOTTOM   = [||undefined||]
genDefunc SAME     = same

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