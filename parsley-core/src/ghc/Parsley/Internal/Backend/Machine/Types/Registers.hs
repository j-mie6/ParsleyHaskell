{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Parsley.Internal.Backend.Machine.Types.Registers (
    module Parsley.Internal.Backend.Machine.Types.Registers, Regs(..), makeRegs
    ) where 

import Data.Kind (Type, Constraint)
import Parsley.Internal.Core.Identifiers (ΣVar (..), SomeΣVar (..))
import Data.Set (Set)
import Data.Some (Some (..))
import Parsley.Internal.Common (Code)
import Language.Haskell.TH (Name)
import Data.List (intercalate)
import qualified Data.Set as Set

{-|
Represents a collection of free registers, preserving their type
information as a heterogeneous list.

@since 1.0.0.0
-}
data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  Regs   :: ΣVar r -> Regs rs -> Regs (r : rs)


{-| 
Represents a collection of registers and their respective `Code` bindings at a given moment
-}
data RegBindNames (rs :: [Type]) where 
  NoName :: RegBindNames '[]
  RegName :: ΣVar x -> Code x -> RegBindNames xs -> RegBindNames (x:xs)


data RegTHNames (rs :: [Type]) where 
  NoTHName :: RegTHNames '[]
  RegTHName :: ΣVar x -> Name -> RegTHNames xs -> RegTHNames (x:xs)


{-|
Converts a set of existential `ΣVar`s into an existential
heterogeneous list of free registers.

@since 1.4.0.0
-}
makeRegs :: Set SomeΣVar -> Some Regs
makeRegs = foldr (\(SomeΣVar σ) (Some rs) -> Some (Regs σ rs)) (Some NoRegs)

fromRegs :: Regs rs -> Set SomeΣVar
fromRegs NoRegs = Set.empty 
fromRegs (Regs r rs) = Set.insert (SomeΣVar r) $ fromRegs rs

debugRegsList :: forall rs. Regs rs -> String
debugRegsList NoRegs = ""
debugRegsList (Regs s rs) = "reg " ++ show s ++ ", " ++ debugRegsList rs