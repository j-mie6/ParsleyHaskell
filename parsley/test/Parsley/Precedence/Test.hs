{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, MultiParamTypeClasses, GADTs #-}
module Parsley.Precedence.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Precedence.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser, empty, Parser)
import Parsley.Patterns (deriveSubtype, deriveLiftedConstructors)
import Parsley.Precedence (Subtype(..))

data Foo where
  Foo :: Bar -> Foo
  Goo :: String -> (Int, Int) -> Foo
  deriving (Eq, Show)
data Bar = Bar Int deriving (Eq, Show)

data X a = X a a

deriveSubtype ''Bar ''Foo
deriveLiftedConstructors "mk" ['X]
deriveLiftedConstructors "mk" ['Bar, 'Goo]

testParser :: Parser (X a)
testParser = mkX empty empty
testParser' :: Parser Foo
testParser' = mkGoo empty

tests :: TestTree
tests = testGroup "Precedence" [
    subtypeTests
  ]

subtypeTests :: TestTree
subtypeTests = testGroup "Subtype should"
  [ testCase "upcast properly" $ upcast (Bar 5) @?= Foo (Bar 5)
  , testCase "downcast properly" $ downcast (Foo (Bar 5)) @?= Just (Bar 5) ]