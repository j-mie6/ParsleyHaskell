module Parsley.Internal.Backend.Machine.Types.InputCharacteristic (
    module Parsley.Internal.Backend.Machine.Types.InputCharacteristic
  ) where

{-|
Provides a way to describe how input is consumed in certain circumstances:

* The input may be always the same on all paths
* The input may always be consumed, but not the same on all paths
* The input may never be consumed in any path
* It may be inconsistent

@since 1.5.0.0
-}
data InputCharacteristic = AlwaysConsumes (Maybe Word)
                         -- ^ On all paths, input must be consumed: `Nothing` when the extact
                         --   amount is inconsistent across paths.
                         | NeverConsumes
                         -- ^ On all paths, no input is consumed.
                         | MayConsume
                         -- ^ The input characteristic is unknown or inconsistent.