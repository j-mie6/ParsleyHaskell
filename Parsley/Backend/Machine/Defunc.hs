{-# LANGUAGE TemplateHaskell,
             GADTs #-}
module Parsley.Backend.Machine.Defunc where

import Parsley.Common.Utils (Code)
import Parsley.Backend.Machine.InputOps (PositionOps(same))
import qualified Parsley.Frontend.Defunc as Frontend (Defunc, genDefunc, genDefunc1, genDefunc2)

data Defunc a where
  USER   :: Frontend.Defunc a -> Defunc a
  BOTTOM :: Defunc a
  SAME   :: PositionOps o => Defunc (o -> o -> Bool)

genDefunc :: Defunc a -> Code a
genDefunc (USER x) = Frontend.genDefunc x
genDefunc BOTTOM   = [||undefined||]
genDefunc SAME     = same

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 (USER f) qx = Frontend.genDefunc1 f qx
genDefunc1 f qx        = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 (USER f) qx qy = Frontend.genDefunc2 f qx qy
genDefunc2 f qx qy        = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a) where
  show (USER x) = show x
  show SAME = "same"
  show BOTTOM = "[[irrelevant]]"