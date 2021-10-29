{-# LANGUAGE PatternSynonyms, CPP #-}
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
#if MIN_VERSION_parsley_core(2,0,0)
#else
    module Frontend,
#endif
    module Backend,
    parse
  ) where

#if MIN_VERSION_parsley_core(2,0,0)
import Parsley.Internal.Backend  (codeGen, eval)
import Parsley.Internal.Frontend (compile)
#endif

import Parsley.Internal.Backend         as Backend    (
    Input,
#if MIN_VERSION_parsley_core(2,0,0)
#else
    codeGen, eval
#endif
  )
import Parsley.Internal.Core            as Core
import Parsley.Internal.Core.Primitives as Primitives (
    pure, (<*>), (*>), (<*),
    (<|>), empty,
    satisfy, lookAhead, try, notFollowedBy,
#if MIN_VERSION_parsley_core(2,0,0)
#else
    chainPre, chainPost,
#endif
    loop,
    Reg, newRegister, get, put,
    conditional, branch,
    debug
  )
import Parsley.Internal.Common.Utils    as THUtils    (Quapplicative(..), WQ, Code, makeQ)
#if MIN_VERSION_parsley_core(2,0,0)
#else
import Parsley.Internal.Frontend        as Frontend   (compile)
#endif
import Parsley.Internal.Trace           as Trace      (Trace(trace))

parse :: (Trace, Input input) => Parser a -> Code (input -> Maybe a)
parse p = [||\input -> $$(eval [||input||] (compile (try p) codeGen))||]