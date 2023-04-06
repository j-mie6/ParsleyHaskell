{-# LANGUAGE DerivingStrategies #-}
module Parsley.Internal.Core.Error (module Parsley.Internal.Core.Error) where

import Data.RangeSet (RangeSet)
import Parsley.Internal.Core.CharPred (CharPred(..))

data BaseError = User UserError
               | SatKnown (RangeSet Char)
               deriving stock (Eq, Show)

data UserError = Empty
               | Fancy [String]
               | Unexpect String
               deriving stock (Eq, Show)

satErr :: CharPred -> BaseError
satErr (Ranges rs) = SatKnown rs
satErr (UserPred _ _) = User Empty
