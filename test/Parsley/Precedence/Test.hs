{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables #-}
module Parsley.Precedence.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Precedence.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser)

tests :: TestTree
tests = testGroup "Precedence should" [

  ]