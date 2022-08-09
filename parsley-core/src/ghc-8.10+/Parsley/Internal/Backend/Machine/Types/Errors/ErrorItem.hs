{-# LANGUAGE DerivingStrategies, DeriveLift #-}
module Parsley.Internal.Backend.Machine.Types.Errors.ErrorItem (
    module Parsley.Internal.Backend.Machine.Types.Errors.ErrorItem
  ) where
import Language.Haskell.TH.Syntax (Lift)

data ErrorItem where
  Raw :: String -> ErrorItem
  Desc :: String -> ErrorItem
  EndOfInput :: ErrorItem
  deriving stock (Lift, Eq, Show, Ord)
