{-# LANGUAGE UndecidableInstances #-}
{-# GHC_OPTIONS Wno-redundant-constraints #-}
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
import Parsley.Backend  (codeGen, Input, Item, eval, prepare)
import Parsley.Frontend (compile)
import GHC.TypeLits     (TypeError, ErrorMessage(Text))

import Parsley.Alternative     as Alternative
import Parsley.Applicative     as Applicative
import Parsley.Core            as Core
import Parsley.Combinator      as Combinator  (item, char, string, satisfy, notFollowedBy, lookAhead, try)
import Parsley.Common.Utils    as THUtils     (code, Quapplicative(..), WQ, Code)
import Parsley.Fold            as Fold        (many, some)
import Parsley.Selective       as Selective
import Parsley.Core.Primitives as Primitives  (debug)

class Token t

instance Token Char
instance {-# INCOHERENT #-} TypeError (Text "Token types must have a `Token` instance and must not be polymorphic") => Token t

runParser :: (Input input, Token (Item input)) => Parser (Item input) a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p codeGen))||]

parseFromFile :: Parser Char a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]
