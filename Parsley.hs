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

import Prelude hiding   (readFile)
import Data.Text.IO     (readFile)
import Parsley.Backend  (codeGen, Input, Token, eval, prepare)
import Parsley.Frontend (compile)

import Parsley.Alternative     as Alternative
import Parsley.Applicative     as Applicative
import Parsley.Core            as Core
import Parsley.Combinator      as Combinator  (item, char, string, satisfy, notFollowedBy, lookAhead, try)
import Parsley.Common.Utils    as THUtils     (code, Quapplicative(..), WQ, Code)
import Parsley.Fold            as Fold        (many, some)
import Parsley.Selective       as Selective
import Parsley.Core.Primitives as Primitives  (debug)

runParser :: (Input input, Token input ~ Char) => Parser Char a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p codeGen))||]

parseFromFile :: Parser Char a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]
