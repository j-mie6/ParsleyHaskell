{-# LANGUAGE MagicHash #-}
module Parsley.Internal.Backend.Machine.Types.Dynamics (
    module Parsley.Internal.Backend.Machine.Types.Dynamics
  ) where

import Data.Kind                                   (Type)
import Parsley.Internal.Backend.Machine.Types.Base (Handler#, Cont#, SubRoutine#, Func)
import Parsley.Internal.Common.Utils               (Code)

type DynHandler s o a = Code (Handler# s o a)
type DynCont s o a x = Code (Cont# s o a x)
type DynSubRoutine s o a x = Code (SubRoutine# s o a x)

type DynFunc (rs :: [Type]) s o a x = Code (Func rs s o a x)
