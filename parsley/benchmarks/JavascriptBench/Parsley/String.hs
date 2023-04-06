{-# OPTIONS_GHC -ddump-splices -ddump-to-file #-}
{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module JavascriptBench.Parsley.String where

import JavascriptBench.Parsley.Parser
import qualified Parsley
import JavascriptBench.Shared

javascriptParsleyS :: String -> Maybe JSProgram
javascriptParsleyS = $$(Parsley.parse javascript)
