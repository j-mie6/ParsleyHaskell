{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Parsley.Internal.Verbose () where

import Parsley.Internal.Trace (Trace(trace))
import qualified Debug.Trace (trace)

instance Trace where
  trace = Debug.Trace.trace