{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, MultiParamTypeClasses, GADTs #-}
module Parsley.Precedence.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Precedence.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser)
import Parsley.Patterns (deriveSubtype)
import Parsley.Precedence (Subtype(..))

data Foo where
  Foo :: Bar -> Foo
  deriving (Eq, Show)
data Bar = Bar Int deriving (Eq, Show)

deriveSubtype ''Bar ''Foo

tests :: TestTree
tests = testGroup "Precedence" [
    subtypeTests
  ]

subtypeTests :: TestTree
subtypeTests = testGroup "Subtype should"
  [ testCase "upcast properly" $ upcast (Bar 5) @?= Foo (Bar 5)
  , testCase "downcast properly" $ downcast (Foo (Bar 5)) @?= Just (Bar 5) ]