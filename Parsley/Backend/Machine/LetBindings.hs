{-# LANGUAGE ExistentialQuantification,
             StandaloneDeriving #-}
module Parsley.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding
  ) where

import Prelude hiding                       (foldr)
import Data.Kind                            (Type)
import Data.Set                             (Set, foldr)
import Parsley.Backend.Machine.Identifiers  (IΣVar, ΣVar(..))
import Parsley.Backend.Machine.Instructions (Instr)
import Parsley.Common                       (Fix4, One)
import Unsafe.Coerce                        (unsafeCoerce)

type Binding o t a x = Fix4 (Instr o t) '[] One x a
data LetBinding o t a x = forall rs. LetBinding (Binding o t a x) (Regs rs)
deriving instance Show (LetBinding o t a x)

makeLetBinding :: Binding o t a x -> Set IΣVar -> LetBinding o t a x
makeLetBinding m rs = LetBinding m (unsafeMakeRegs rs)

data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)
deriving instance Show (Regs rs)

unsafeMakeRegs :: Set IΣVar -> Regs rs
unsafeMakeRegs =  foldr (\σ rs -> unsafeCoerce (FreeReg (ΣVar σ) rs)) (unsafeCoerce NoRegs)