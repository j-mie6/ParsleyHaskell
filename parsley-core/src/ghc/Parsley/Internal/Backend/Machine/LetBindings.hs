{-# LANGUAGE PatternSynonyms #-}
module Parsley.Internal.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding
  ) where

import Prelude hiding                                (foldr)
import Data.Kind                                     (Type)
import Data.Set                                      (Set, foldr)
import Data.Some                                     (Some, pattern Some)
import Parsley.Internal.Backend.Machine.Identifiers  (ΣVar, SomeΣVar(..))
import Parsley.Internal.Backend.Machine.Instructions (Instr)
import Parsley.Internal.Common                       (Fix4, One)

type Binding o a x = Fix4 (Instr o) '[] One x a
data LetBinding o a x = LetBinding (Binding o a x) (Some Regs)

makeLetBinding :: Binding o a x -> Set SomeΣVar -> LetBinding o a x
makeLetBinding m rs = LetBinding m (makeRegs rs)

data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)

makeRegs :: Set SomeΣVar -> Some Regs
makeRegs = foldr (\(SomeΣVar σ) (Some rs) -> Some (FreeReg σ rs)) (Some NoRegs)