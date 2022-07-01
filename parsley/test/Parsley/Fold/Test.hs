{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Parsley.Fold.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Fold.Parsers as Parsers

import Prelude hiding ()

tests :: TestTree
tests = testGroup "Fold" [ prefixTests
                         , postfixTests
                         , manyrTests
                         , somerTests
                         , manylTests
                         , somelTests
                         , chainlTests
                         , chainrTests
                         , infixl1Tests
                         , infixr1Tests
                         , manyTests
                         , skipManyTests
                         , sepByTests
                         , endByTests
                         , sepEndByTests]

plusOne :: String -> Maybe Int
plusOne = $$(runParserMocked Parsers.plusOne [||Parsers.plusOne||])

plusOne' :: String -> Maybe Int
plusOne' = $$(runParserMocked Parsers.plusOne' [||Parsers.plusOne'||])

plusOnePure :: String -> Maybe Int
plusOnePure = $$(runParserMocked Parsers.plusOnePure [||Parsers.plusOnePure||])

prefixTests :: TestTree
prefixTests = testGroup "prefix should"
  [ testCase "parse an operatorless value" $ do
      plusOne "1" @?= Just 1
      plusOne "" @?= Nothing
      plusOnePure "" @?= Just 1
  , testCase "parser all operators that precede" $ do
      plusOne "++++1" @?= Just 3
      plusOne' "++++1" @?= Just 3
      plusOnePure "+" @?= Just 0
  , testCase "fail if an operator fails after consuming input" $ plusOne "+++1" @?= Nothing
  ]

onePlus :: String -> Maybe Int
onePlus = $$(runParserMocked Parsers.onePlus [||Parsers.onePlus||])

onePlus' :: String -> Maybe Int
onePlus' = $$(runParserMocked Parsers.onePlus' [||Parsers.onePlus'||])

postfixTests :: TestTree
postfixTests = testGroup "postfix should"
  [ testCase "require an initial value" $ do
      onePlus "1" @?= Just 1
      onePlus "" @?= Nothing
  , testCase "parser all operators that follow" $ onePlus "1++++" @?= Just 3
  , testCase "fail if an operator fails after consuming input" $ onePlus "1+++" @?= Nothing
  , testCase "not fail if the operator fails with try" $ onePlus' "1+++" @?= Just 2
  ]

manyrTests :: TestTree
manyrTests = testGroup "manyr should" []

somerTests :: TestTree
somerTests = testGroup "somer should" []

manylTests :: TestTree
manylTests = testGroup "manyl should" []

somelTests :: TestTree
somelTests = testGroup "somel should" []

chainlTests :: TestTree
chainlTests = testGroup "chainl should" [] -- chainl1 chainl

chainrTests :: TestTree
chainrTests = testGroup "chainr should" [] -- chainr1 chainr

infixl1Tests :: TestTree
infixl1Tests = testGroup "infixl1 should" []

infixr1Tests :: TestTree
infixr1Tests = testGroup "infixr1 should" []

manyAA :: String -> Maybe [String]
manyAA = $$(runParserMocked Parsers.manyAA [||Parsers.manyAA||])

someA :: String -> Maybe String
someA = $$(runParserMocked Parsers.someA [||Parsers.someA||])

many2A :: String -> Maybe String
many2A = $$(runParserMocked Parsers.many2A [||Parsers.many2A||])

manyTests :: TestTree
manyTests = testGroup "many should"
  [ testCase "succeed on empty input" $ do
      manyAA "" @?= Just []
      someA "" @?= Nothing
      many2A "" @?= Nothing
      many2A "a" @?= Nothing
  , testCase "succeed when given an input" $ do
      manyAA "aa" @?= Just ["aa"]
      someA "aa" @?= Just "aa"
      many2A "aaa" @?= Just "aaa"
  , testCase "fail when partial" $ manyAA "a" @?= Nothing
  ]

skipManyTests :: TestTree
skipManyTests = testGroup "skipMany should" [] -- skipMany skipManyN skipSome

sepByTests :: TestTree
sepByTests = testGroup "sepBy should" [] -- sepBy sepBy1

endByTests :: TestTree
endByTests = testGroup "endBy should" [] -- endBy endBy1

sepEndByTests :: TestTree
sepEndByTests = testGroup "sepEndBy should" [] -- sepEndBy sepEndBy1
