{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables #-}
module Parsley.Alternative.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Alternative.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser)

tests :: TestTree
tests = testGroup "Alternative" [ coproductTests
                                , optionTests
                                , choiceTests
                                , manyTillTests
                                ]

coproductTests :: TestTree
coproductTests = testGroup "<+> should" [] -- <+>

optionTests :: TestTree
optionTests = testGroup "option should" [] -- optional, optionally, option, maybeP

choiceTests :: TestTree
choiceTests = testGroup "choice should" [] -- choice

manyTillTests :: TestTree
manyTillTests = testGroup "manyTill should" [] --manyTill