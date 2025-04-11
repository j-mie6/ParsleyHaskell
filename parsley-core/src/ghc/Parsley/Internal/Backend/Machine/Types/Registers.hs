module Parsley.Internal.Backend.Machine.Types.Registers (
    module Parsley.Internal.Backend.Machine.Types.Registers, Regs(..), makeRegs
    ) where 

import Data.Kind (Type)
import Parsley.Internal.Core.Identifiers (ΣVar, SomeΣVar (..))
import Data.Set (Set)
import Data.Some (Some (..))

{-|
Represents a collection of free registers, preserving their type
information as a heterogeneous list.

@since 1.0.0.0
-}
data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  Regs   :: ΣVar r -> Regs rs -> Regs (r : rs)


{-|
Converts a set of existential `ΣVar`s into an existential
heterogeneous list of free registers.

@since 1.4.0.0
-}
makeRegs :: Set SomeΣVar -> Some Regs
makeRegs = foldr (\(SomeΣVar σ) (Some rs) -> Some (Regs σ rs)) (Some NoRegs)