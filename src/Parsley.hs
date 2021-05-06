{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Parsley.Internal.Backend  (codeGen, Input, eval, prepare)
import Parsley.Internal.Frontend (compile)
import Parsley.Internal.Trace    (Trace(trace))

import Parsley.Alternative              as Alternative
import Parsley.Applicative              as Applicative
import Parsley.Combinator               as Combinator  (item, char, string, satisfy, notFollowedBy, lookAhead, try)
import Parsley.Fold                     as Fold        (many, some)
import Parsley.Internal.Core            as Core
import Parsley.Internal.Common.Utils    as THUtils     ({-code, -}Quapplicative(..), WQ, Code)
import Parsley.Internal.Core.Primitives as Primitives  (debug)
import Parsley.Selective                as Selective

runParser :: (Trace, Input input) => Parser a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p codeGen))||]

parseFromFile :: Trace => Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]

instance {-# INCOHERENT #-} Trace where
  trace = flip const