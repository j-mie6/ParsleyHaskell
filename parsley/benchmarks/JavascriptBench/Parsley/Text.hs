{-# OPTIONS_GHC -ddump-splices -ddump-to-file #-}
{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module JavascriptBench.Parsley.Text where

import JavascriptBench.Parsley.Parser
import qualified Parsley
import JavascriptBench.Shared
import Data.Text       (Text)

javascriptParsleyT :: Text -> Maybe JSProgram
javascriptParsleyT = $$(Parsley.parse javascript)
