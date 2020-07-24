{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell,
             UnboxedTuples,
             NoMonomorphismRestriction,
             FlexibleInstances #-}
module LinkedParsers where

import qualified Parsers
import qualified Parsley

$(Parsley.buildLoadableParser "linkTest" [t|Char|] Parsers.linkTest)