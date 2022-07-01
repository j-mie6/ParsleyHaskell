{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Parsley
Description : Main functionality exports
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the core execution functions `parse` and `parseFromFile`.
It exports the `Parser` type, as well as the `ParserOps` typeclass, which may be needed
as a constraint to create more general combinators. It also exports several of the more
important modules and functionality in particular the core set of combinators.

@since 0.1.0.0
-}
module Parsley (
    parse, parseFromFile,
    module Core,
    module Applicative,
    module Alternative,
    module Selective,
    module Combinator,
    module Char,
    module Fold,
    module Debug,
    module THUtils,
  ) where

import Prelude hiding            (readFile)
import Data.Text.IO              (readFile)
import Parsley.InputExtras       (Text16(..))
import Parsley.Internal          (Input, Trace(trace))

import Parsley.Alternative              as Alternative
import Parsley.Applicative              as Applicative
import Parsley.Char                     as Char        (item, char, string, satisfy)
import Parsley.Combinator               as Combinator  (notFollowedBy, lookAhead, try)
import Parsley.Fold                     as Fold        (many, some)
import Parsley.Internal                 as Core        (Parser)
import Parsley.ParserOps                as Core        (ParserOps)
import Parsley.Internal                 as THUtils     (Quapplicative(..), WQ, Code)
import Parsley.Debug                    as Debug       (debug)
import Parsley.Selective                as Selective

import qualified Parsley.Internal as Internal (parse)

{-|
The standard way to compile a parser, it returns `Code`, which means
that it must be /spliced/ into a function definition to produce a
function of type @input -> Maybe a@ for a chosen input type. As an example:

/In @Parser.hs@/:

> helloParsley :: Parser String
> helloParsley = string "hello Parsley!"

/In @Main.hs@/:

> parseHelloParsley :: String -> Maybe String
> parseHelloParsley = $$(parse helloParsley)

Note that the definition of the parser __must__ be in a separate module to
the splice (@$$@).

See `Input` for what the valid input types for Parsley are.

The `Trace` instance is used to enable verbose debugging output for
the compilation pipeline when "Parsley.Internal.Verbose" is imported.

@since 2.0.0.0
-}
parse :: (Trace, Input input)
      => Parser a                -- ^ The parser to be compiled
      -> Code (input -> Maybe a) -- ^ The generated parsing function
parse = Internal.parse

{-|
This function generates a function that reads input from a file
and parses it. The input files contents are treated as `Text16`.

See `parse` for more information.

@since 0.1.0.0
-}
parseFromFile :: Trace
              => Parser a                        -- ^ The parser to be compiled
              -> Code (FilePath -> IO (Maybe a)) -- ^ The generated parsing function
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(parse p) (Text16 input))||]

{-|
The default instance for `Trace`, which disables all debugging output about the parser compilation
process. If "Parsley.Internal.Verbose" is imported, this instance will be supersceded.

@since 0.1.0.0
-}
instance {-# INCOHERENT #-} Trace where
  trace = flip const
