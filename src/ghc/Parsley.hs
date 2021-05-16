{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Parsley
Description : Main functionality exports
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the core execution functions `runParser` and `parseFromFile`.
It exports the `Parser` type, as well as the `ParserOps` typeclass, which may be needed
as a constraint to create more general combinators. It also exports several of the more
important modules and functionality in particular the core set of combinators.

@since 0.1.0.0
-}
module Parsley (
    module Parsley,
    module Core,
    module Primitives,
    module Applicative,
    module Alternative,
    module Selective,
    module Combinator,
    module Fold,
    module THUtils,
  ) where

import Prelude hiding            (readFile)
import Data.Text.IO              (readFile)
import Parsley.InputExtras       (Text16(..))
import Parsley.Internal.Backend  (codeGen, Input, eval)
import Parsley.Internal.Frontend (compile)
import Parsley.Internal.Trace    (Trace(trace))

import Parsley.Alternative              as Alternative
import Parsley.Applicative              as Applicative
import Parsley.Combinator               as Combinator  (item, char, string, satisfy, notFollowedBy, lookAhead, try)
import Parsley.Fold                     as Fold        (many, some)
import Parsley.Internal.Core            as Core        (Parser, ParserOps)
import Parsley.Internal.Common.Utils    as THUtils     (Quapplicative(..), WQ, Code)
import Parsley.Internal.Core.Primitives as Primitives  (debug)
import Parsley.Selective                as Selective

runParser :: (Trace, Input input) => Parser a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval [||input||] (compile p codeGen))||]

parseFromFile :: Trace => Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]

instance {-# INCOHERENT #-} Trace where
  trace = flip const