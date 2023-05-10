{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Main where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Regression.Parsers as Parsers

import Parsley (parse)
import Parsley.InputExtras (CharList(..))

import Parsley.Internal.Verbose ()

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Regression Tests" [ issue26, issue41 ]

issue26 :: TestTree
issue26 = testGroup "#26 Coin draining on bindings is wrong"
  [ testCase "" $ issue26_ex1 "123ab" @?= Nothing
  , testCase "" $ issue26_ex2 "123ab" @?= Nothing
  ]

issue41 :: TestTree
issue41 = testGroup "#41 Length-factoring can cross `put` but shouldn't"
  [ testCase "it should work when enough input is given" $ issue41_ex1 "ab" @?= Just True
  , testCase "it should work when enough input is given" $ issue41_ex1 "ac" @?= Just True
  , testCase "it should prevent factoring" $ issue41_ex1 "a" @?= Just True
  , testCase "it should prevent factoring" $ issue41_ex2 "a" @?= Just False
  , testCase "it should prevent factoring" $ issue41_ex2 "b" @?= Just True
  , testCase "it should prevent factoring" $ issue41_ex2 "ab" @?= Just False
  , testCase "it should prevent factoring" $ issue41_ex2 "abc" @?= Just False
  ]

issue26_ex1 :: String -> Maybe ()
issue26_ex1 = $$(Parsley.parse Parsers.issue26_ex1)

issue26_ex2 :: String -> Maybe ()
issue26_ex2 = $$(Parsley.parse Parsers.issue26_ex2)

issue41_ex1 :: String -> Maybe Bool
issue41_ex1 = $$(Parsley.parse Parsers.issue41_ex1)

issue41_ex2 :: String -> Maybe Bool
issue41_ex2 = $$(Parsley.parse Parsers.issue41_ex2)
