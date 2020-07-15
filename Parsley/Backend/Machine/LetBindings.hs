{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             PolyKinds,
             KindSignatures,
             StandaloneDeriving,
             ExistentialQuantification #-}
module Parsley.Backend.Machine.LetBindings (module Parsley.Backend.Machine.LetBindings) where

import Prelude hiding                       (foldr)
import Data.Set                             (Set, foldr)
import Data.STRef                           (STRef)
import Parsley.Backend.Machine.Identifiers  (IΣVar, ΣVar(..))
import Parsley.Backend.Machine.Instructions (Instr)
import Parsley.Common                       (Fix4, One, Code)
import Unsafe.Coerce                        (unsafeCoerce)

data LetBinding o a x = forall rs. LetBinding (Fix4 (Instr o) '[] One x a) (Regs rs)
deriving instance Show (LetBinding o a x)

makeLetBinding :: Fix4 (Instr o) '[] One x a -> Set IΣVar -> LetBinding o a x
makeLetBinding m rs = LetBinding m (unsafeMakeRegs rs)

data Regs rs where
  NoRegs :: Regs '[]
  Reg :: ΣVar r -> Regs rs -> Regs (r : rs)
deriving instance Show (Regs rs)

unsafeMakeRegs :: Set IΣVar -> Regs rs
unsafeMakeRegs =  foldr (\σ rs -> unsafeCoerce (Reg (ΣVar σ) rs)) (unsafeCoerce NoRegs)