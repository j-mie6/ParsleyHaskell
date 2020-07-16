{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             PolyKinds,
             KindSignatures,
             StandaloneDeriving,
             ExistentialQuantification #-}
module Parsley.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding
  ) where

import Prelude hiding                       (foldr)
import Data.Set                             (Set, foldr)
import Data.STRef                           (STRef)
import Parsley.Backend.Machine.Identifiers  (IΣVar, ΣVar(..))
import Parsley.Backend.Machine.Instructions (Instr)
import Parsley.Common                       (Fix4, One, Code)
import Unsafe.Coerce                        (unsafeCoerce)

type Binding o a x = Fix4 (Instr o) '[] One x a
data LetBinding o a x = forall rs. LetBinding (Binding o a x) (Regs rs)
deriving instance Show (LetBinding o a x)

makeLetBinding :: Binding o a x -> Set IΣVar -> LetBinding o a x
makeLetBinding m rs = LetBinding m (unsafeMakeRegs rs)

data Regs (rs :: [*]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)
deriving instance Show (Regs rs)

unsafeMakeRegs :: Set IΣVar -> Regs rs
unsafeMakeRegs =  foldr (\σ rs -> unsafeCoerce (FreeReg (ΣVar σ) rs)) (unsafeCoerce NoRegs)