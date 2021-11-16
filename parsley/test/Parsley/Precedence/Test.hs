{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, MultiParamTypeClasses, GADTs, DeriveGeneric #-}
--{-# OPTIONS_GHC -ddump-splices #-}
module Parsley.Precedence.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Precedence.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser, empty, Parser)
--import Parsley.Patterns (deriveSubtype, deriveLiftedConstructors, deriveDeferredConstructors, Pos)
--import Parsley.Precedence (Subtype(..))
--import GHC.Generics (Generic)

{-data Foo where
  Foo :: Bar -> Foo
  Goo :: String -> Pos -> Int -> Foo
  deriving (Eq, Show, Generic)
newtype Bar = Bar Int deriving (Eq, Show, Generic)

data X a = X a a Pos

deriveSubtype ''Bar ''Foo
deriveLiftedConstructors "mk" ['X]
deriveLiftedConstructors "mk" ['Bar, 'Goo]
deriveDeferredConstructors "mkD" ['X]

testParser :: Parser (X a)
testParser = mkX empty empty
testParser' :: Parser Foo
testParser' = mkGoo empty empty
testParser'' :: Parser (a -> a -> X a)
testParser'' = mkDX-}

tests :: TestTree
tests = testGroup "Precedence" [
    precHomoTests
    --subtypeTests
  ]

expr :: String -> Maybe Parsers.Expr
expr = $$(runParserMocked Parsers.expr [||Parsers.expr||])

precHomoTests :: TestTree
precHomoTests = testGroup "precHomo should"
  [ testCase "parse precedence with correct associativity" $ expr "1+3*negate5+4" @?=
        Just (Parsers.Add (Parsers.Num 1)
                          (Parsers.Add (Parsers.Mul (Parsers.Num 3)
                                                    (Parsers.Negate (Parsers.Num 5)))
                                       (Parsers.Num 4)))]

{-subtypeTests :: TestTree
subtypeTests = testGroup "Subtype should"
  [ testCase "upcast properly" $ upcast (Bar 5) @?= Foo (Bar 5)
  , testCase "downcast properly" $ downcast (Foo (Bar 5)) @?= Just (Bar 5) ]-}