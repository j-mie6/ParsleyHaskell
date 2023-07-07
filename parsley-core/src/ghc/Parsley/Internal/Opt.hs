module Parsley.Internal.Opt (module Parsley.Internal.Opt) where

import Data.Ratio ((%))

on, off :: Bool
on = True
off = False

defaultInlineThreshold :: Maybe Rational
defaultInlineThreshold = Just (13 % 10)

data Flags = Flags { lawBasedOptimisations :: Bool
                   , termNormalisation     :: Bool
                   , inlineThreshold       :: Maybe Rational
                   -- TODO: merge these together
                   , lengthCheckFactoring  :: Bool -- TODO:
                   , leadCharFactoring     :: Bool -- TODO:
                   , factorAheadOfJoins    :: Bool -- TODO:
                   , reclaimInput          :: Bool -- TODO:
                   --, closeFreeRegisters    :: Bool
                   }

none, fast, full :: Flags
none = Flags { lawBasedOptimisations = off
             , termNormalisation     = off
             , inlineThreshold       = Nothing
             , lengthCheckFactoring  = off
             , leadCharFactoring     = off
             , factorAheadOfJoins    = off
             , reclaimInput          = off
             --, closeFreeRegisters    = off
             }
fast = full  --{ }
full = Flags { lawBasedOptimisations = on
             , termNormalisation     = on
             , inlineThreshold       = defaultInlineThreshold
             , lengthCheckFactoring  = on
             , leadCharFactoring     = on
             , factorAheadOfJoins    = on
             , reclaimInput          = on
             --, closeFreeRegisters    = on
             }
