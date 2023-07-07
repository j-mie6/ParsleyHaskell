module Parsley.Internal.Opt (module Parsley.Internal.Opt) where

import Data.Ratio ((%))

on, off :: Bool
on = True
off = False

defaultInlineThreshold :: Maybe Rational
defaultInlineThreshold = Just (13 % 10)

data Flags = Flags { lawBasedOptimisations :: Bool
                   , fullyStaticPredicates :: Bool -- TODO:
                   , termNormalisation     :: Bool -- TODO:
                   , inlineThreshold       :: Maybe Rational
                   -- TODO: merge these together
                   , lengthCheckFactoring  :: Bool -- TODO:
                   , leadCharFactoring     :: Bool -- TODO:
                   , factorAheadOfJoins    :: Bool -- TODO:
                   , reclaimInput          :: Bool -- TODO:
                   , closeFreeRegisters    :: Bool -- TODO:
                   }

none, fast, full :: Flags
none = Flags { lawBasedOptimisations = off
             , fullyStaticPredicates = off
             , termNormalisation     = off
             , inlineThreshold       = Nothing
             , lengthCheckFactoring  = off
             , leadCharFactoring     = off
             , factorAheadOfJoins    = off
             , reclaimInput          = off
             , closeFreeRegisters    = off
             }
fast = Flags { lawBasedOptimisations = on
             , fullyStaticPredicates = off
             , termNormalisation     = on
             , inlineThreshold       = defaultInlineThreshold
             , lengthCheckFactoring  = on
             , leadCharFactoring     = on
             , factorAheadOfJoins    = on
             , reclaimInput          = on
             , closeFreeRegisters    = on
             }
full = Flags { lawBasedOptimisations = on
             , fullyStaticPredicates = on
             , termNormalisation     = on
             , inlineThreshold       = defaultInlineThreshold
             , lengthCheckFactoring  = on
             , leadCharFactoring     = on
             , factorAheadOfJoins    = on
             , reclaimInput          = on
             , closeFreeRegisters    = on
             }
