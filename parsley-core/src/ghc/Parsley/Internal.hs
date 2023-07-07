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
    module Backend,
    parse, parseWithOpts
  ) where

import Parsley.Internal.Backend  (codeGen, eval)
import Parsley.Internal.Frontend (compile)

import Parsley.Internal.Backend         as Backend    (
    Input,
  )
import Parsley.Internal.Core            as Core
import Parsley.Internal.Core.Primitives as Primitives (
    pure, (<*>), (*>), (<*),
    (<|>), empty,
    satisfy, lookAhead, try, notFollowedBy,
    loop,
    Reg, newRegister, get, put,
    conditional, branch,
    line, col,
    debug
  )
import Parsley.Internal.Common.Utils    as THUtils    (Quapplicative(..), WQ, Code, makeQ)
import Parsley.Internal.Trace           as Trace      (Trace(trace))

import qualified Parsley.Internal.Opt   as Opt

parse :: (Trace, Input input) => Parser a -> Code (input -> Maybe a)
parse = parseWithOpts Opt.fast

parseWithOpts :: (Trace, Input input) => Opt.Flags -> Parser a -> Code (input -> Maybe a)
parseWithOpts flags p = [||\input -> $$(eval flags [||input||] (compile flags (try p) (codeGen flags)))||]
