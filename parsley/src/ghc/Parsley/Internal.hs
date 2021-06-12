{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Internal
Description : The gateway into the internals: here be monsters!
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : unstable

This module exposes all of the /required/ functionality found in the internals of the library out
to the user API.

@since 0.1.0.0
-}
module Parsley.Internal (
    module Core,
    module Primitives,
    module THUtils,
    module Trace,
    module Frontend,
    module Backend
  ) where

import Parsley.Internal.Backend         as Backend    (codeGen, Input, eval)
import Parsley.Internal.Core            as Core
import Parsley.Internal.Core.Primitives as Primitives (
    pure, (<*>), (*>), (<*),
    (<|>), empty,
    satisfy, lookAhead, try, notFollowedBy,
    chainPre, chainPost,
    Reg, newRegister, get, put,
    conditional, branch,
    debug
  )
import Parsley.Internal.Common.Utils    as THUtils    (Quapplicative(..), WQ, Code, makeQ)
import Parsley.Internal.Frontend        as Frontend   (compile)
import Parsley.Internal.Trace           as Trace      (Trace(trace))