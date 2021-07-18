{-# LANGUAGE MagicHash,
             TypeFamilies #-}
module Parsley.Internal.Backend.Machine.Types.Base (
    module Parsley.Internal.Backend.Machine.Types.Base
  ) where

import Control.Monad.ST                          (ST)
import Data.STRef                                (STRef)
import Data.Kind                                 (Type)
import Parsley.Internal.Backend.Machine.InputRep (Rep)

type Handler# s o a = Rep o -> ST s (Maybe a)
type Cont# s o a x = x -> Rep o -> ST s (Maybe a)
type SubRoutine# s o a x = Cont# s o a x -> Rep o -> Handler# s o a -> ST s (Maybe a)

type family Func (rs :: [Type]) s o a x where
  Func '[] s o a x      = SubRoutine# s o a x
  Func (r : rs) s o a x = STRef s r -> Func rs s o a x