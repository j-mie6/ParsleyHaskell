{-# LANGUAGE ExistentialQuantification,
             StandaloneDeriving #-}
module Parsley.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding(..)
  ) where

import Prelude hiding                       (foldr)
import Data.Kind                            (Type)
import Data.Set                             (Set, foldr)
import Parsley.Backend.Machine.Identifiers  (IΣVar, ΣVar(..))
import Parsley.Backend.Machine.Instructions (Instr)
import Parsley.Common                       (Fix4, One)
import Unsafe.Coerce                        (unsafeCoerce)

newtype Binding o x = Binding (forall r. Fix4 (Instr o) '[] One x r)
data LetBinding o x = forall rs. LetBinding (Binding o x) (Regs rs)

deriving instance Show (LetBinding o x)
instance Show (Binding o x) where
  show (Binding b) = show b

makeLetBinding :: Binding o x -> Set IΣVar -> LetBinding o x
makeLetBinding m rs = LetBinding m (unsafeMakeRegs rs)

data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)
deriving instance Show (Regs rs)

unsafeMakeRegs :: Set IΣVar -> Regs rs
unsafeMakeRegs =  foldr (\σ rs -> unsafeCoerce (FreeReg (ΣVar σ) rs)) (unsafeCoerce NoRegs)