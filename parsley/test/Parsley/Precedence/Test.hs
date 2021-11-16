{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, MultiParamTypeClasses, GADTs, DeriveGeneric, TypeApplications, FlexibleInstances, FlexibleContexts #-}
--{-# OPTIONS_GHC -ddump-splices #-}
module Parsley.Precedence.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Precedence.Parsers as Parsers

import Prelude hiding (pred)
import Parsley (runParser, empty, Parser)
--import Parsley.Patterns (deriveSubtype, deriveLiftedConstructors, deriveDeferredConstructors, Pos)
import Parsley.Precedence (Subtype(..))
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
    precHomoTests,
    precedenceTests
    --subtypeTests
  ]

expr :: String -> Maybe Parsers.Expr
expr = $$(runParserMocked Parsers.expr [||Parsers.expr||])

pred :: String -> Maybe Parsers.Pred
pred = $$(runParserMocked Parsers.pred [||Parsers.pred||])

precHomoTests :: TestTree
precHomoTests = testGroup "precHomo should"
  [ testCase "parse precedence with correct associativity" $ expr "1+3*negate5+4" @?=
        Just (Parsers.Add (Parsers.Num 1)
                          (Parsers.Add (Parsers.Mul (Parsers.Num 3)
                                                    (Parsers.Negate (Parsers.Num 5)))
                                       (Parsers.Num 4)))]

instance Subtype a a where
  upcast = id
  downcast = Just

upcast' :: Parsers.Atom -> Parsers.Term
upcast' = upcast @Parsers.Not . upcast

upcast'' :: Subtype x Parsers.Term => x -> Parsers.Pred
upcast'' = Parsers.OfTerm . upcast

precedenceTests :: TestTree
precedenceTests = testGroup "precedence should"
  [ testCase "parse precedence with correct associativity" $ pred "T|F|(T|!F)&F" @?=
        Just (Parsers.Or (upcast' Parsers.T)
                         (Parsers.Or (upcast' Parsers.F)
                                     (upcast'' (Parsers.And (upcast (Parsers.Parens
                                                               (Parsers.Or (upcast' Parsers.T)
                                                                           (upcast'' (Parsers.Not (upcast Parsers.F))))))
                                                            (upcast' Parsers.F)))))]

{-subtypeTests :: TestTree
subtypeTests = testGroup "Subtype should"
  [ testCase "upcast properly" $ upcast (Bar 5) @?= Foo (Bar 5)
  , testCase "downcast properly" $ downcast (Foo (Bar 5)) @?= Just (Bar 5) ]-}