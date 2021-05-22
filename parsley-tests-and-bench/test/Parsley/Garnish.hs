{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Parsley.Garnish (module LiftPlugin) where

import LiftPlugin (LiftTo(..))
import Parsley (Quapplicative(makeQ))

instance Quapplicative q => LiftTo q where code x = makeQ x [||x||]