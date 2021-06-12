{-# LANGUAGE ExistentialQuantification,
             StandaloneDeriving,
             DerivingStrategies #-}
module Parsley.Internal.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding
  ) where

import Prelude hiding                                (foldr)
import Data.Kind                                     (Type)
import Data.Set                                      (Set, foldr)
import Parsley.Internal.Backend.Machine.Identifiers  (IΣVar, ΣVar(..))
import Parsley.Internal.Backend.Machine.Instructions (Instr)
import Parsley.Internal.Common                       (Fix4, One)
import Unsafe.Coerce                                 (unsafeCoerce)

type Binding o a x = Fix4 (Instr o) '[] One x a
data LetBinding o a x = forall rs. LetBinding (Binding o a x) (Regs rs)
deriving stock instance Show (LetBinding o a x)

makeLetBinding :: Binding o a x -> Set IΣVar -> LetBinding o a x
makeLetBinding m rs = LetBinding m (unsafeMakeRegs rs)

data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)
deriving stock instance Show (Regs rs)

unsafeMakeRegs :: Set IΣVar -> Regs rs
unsafeMakeRegs =  foldr (\σ rs -> unsafeCoerce (FreeReg (ΣVar σ) rs)) (unsafeCoerce NoRegs)