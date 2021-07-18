module Parsley.Internal.Backend.Machine.Types (
    module Parsley.Internal.Backend.Machine.Types,
    module Parsley.Internal.Backend.Machine.Types.Base,
    module Parsley.Internal.Backend.Machine.Types.Statics
  ) where

import Control.Monad.Reader                            (Reader, runReader)
import Control.Monad.ST                                (ST)
import Parsley.Internal.Backend.Machine.Types.Base    (Func)
import Parsley.Internal.Backend.Machine.Types.Context (Ctx)
import Parsley.Internal.Backend.Machine.Types.State   (Γ)
import Parsley.Internal.Backend.Machine.Types.Statics (QSubRoutine, qSubRoutine)
import Parsley.Internal.Common.Utils                  (Code)

type MachineMonad s o xs n r a = Reader (Ctx s o a) (Γ s o xs n r a -> Code (ST s (Maybe a)))

newtype Machine s o xs n r a = Machine { getMachine :: MachineMonad s o xs n r a }

run :: Machine s o xs n r a -> Γ s o xs n r a -> Ctx s o a -> Code (ST s (Maybe a))
run = flip . runReader . getMachine