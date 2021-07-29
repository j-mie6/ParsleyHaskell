{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Parsley.Regressions.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Regressions.Parsers as Parsers

import Parsley (runParser)
import Parsley.InputExtras (CharList(..))

tests :: TestTree
tests = testGroup "Regressions" [ issue26 ]

issue26 :: TestTree
issue26 = testGroup "#26 Coin draining on bindings is wrong"
  [ testCase "" $ issue26_ex1 (CharList "123ab") @?= Nothing
  , testCase "" $ issue26_ex2 (CharList "123ab") @?= Nothing
  ]

issue26_ex1 :: CharList -> Maybe ()
issue26_ex1 = $$(Parsley.runParser Parsers.issue26_ex1)

issue26_ex2 :: CharList -> Maybe ()
issue26_ex2 = $$(Parsley.runParser Parsers.issue26_ex2)