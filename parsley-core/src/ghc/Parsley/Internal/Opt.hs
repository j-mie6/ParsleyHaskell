module Parsley.Internal.Opt (module Parsley.Internal.Opt) where

import Data.Ratio ((%))

on, off :: Bool
on = True
off = False

defaultPrimaryInlineThreshold :: Maybe Rational
defaultPrimaryInlineThreshold = Just $ 13 % 10 * {- Occurrence Bias -} 3

defaultSecondaryInlineThreshold :: Maybe Rational
defaultSecondaryInlineThreshold = Just $ 13 % 10

data Flags = Flags { lawBasedOptimisations    :: !Bool
                   , termNormalisation        :: !Bool
                   , primaryInlineThreshold   :: !(Maybe Rational)
                   , secondaryInlineThreshold :: !(Maybe Rational)
                   -- TODO: merge these together
                   , lengthCheckFactoring     :: !Bool
                   , leadCharFactoring        :: !Bool
                   , factorAheadOfJoins       :: !Bool
                   , reclaimInput             :: !Bool
                   , deduceFailPath           :: !Bool
                   --, closeFreeRegisters       :: !Bool
                   }

none, fast, full :: Flags
none = Flags { lawBasedOptimisations    = off
             , termNormalisation        = off
             , primaryInlineThreshold   = Nothing
             , secondaryInlineThreshold = Nothing
             , lengthCheckFactoring     = off
             , leadCharFactoring        = off
             , factorAheadOfJoins       = off
             , reclaimInput             = off
             , deduceFailPath           = off
             --, closeFreeRegisters       = off
             }
fast = full  --{ }
full = Flags { lawBasedOptimisations    = on
             , termNormalisation        = on
             , primaryInlineThreshold   = defaultPrimaryInlineThreshold
             , secondaryInlineThreshold = defaultSecondaryInlineThreshold
             , lengthCheckFactoring     = on
             , leadCharFactoring        = on
             , factorAheadOfJoins       = on
             , reclaimInput             = on
             , deduceFailPath           = on
             --, closeFreeRegisters       = on
             }
