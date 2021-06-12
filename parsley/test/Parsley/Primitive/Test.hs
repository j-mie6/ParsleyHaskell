{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Parsley.Primitive.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Primitive.Parsers as Parsers

import Parsley (runParser, empty)

tests :: TestTree
tests = testGroup "Primitive" [ pureTests
                              , apTests
                              , thenTests
                              , prevTests
                              , altTests
                              , emptyTests
                              , satisfyTests
                              , lookAheadTests
                              , notFollowedByTests
                              , tryTests
                              , branchTests
                              , conditionalTests
                              , recursionTests
                              ]

pure7 :: String -> Maybe Int
pure7 = $$(runParserMocked Parsers.pure7 [||Parsers.pure7||])

pureTests :: TestTree
pureTests = testGroup "pure should"
  [ testCase "not need to consume input" $ pure7 "" @?= Just 7
  , testCase "not fail if there is input" $ pure7 "a" @?= Just 7
  ]

apTests :: TestTree
apTests = testGroup "<*> should" []

thenTests :: TestTree
thenTests = testGroup "*> should" []

prevTests :: TestTree
prevTests = testGroup "<* should" []

abOrC :: String -> Maybe String
abOrC = $$(runParserMocked Parsers.abOrC [||Parsers.abOrC||])

abOrCThenD :: String -> Maybe String
abOrCThenD = $$(runParserMocked Parsers.abOrCThenD [||Parsers.abOrCThenD||])

altTests :: TestTree
altTests = testGroup "<|> should"
  [ testCase "take the left branch if it succeeds" $ do
      abOrC "ab" @?= Just "ab"
      abOrCThenD "abd" @?= Just "ab"
  , testCase "take the right branch if left failed without consumption" $ do
      abOrC "c" @?= Just "c"
      abOrC "d" @?= Nothing
      abOrCThenD "cd" @?= Just "c"
      abOrCThenD "d" @?= Nothing
  , testCase "fail if the left branch fails and consumes input" $ abOrC "a" @?= Nothing
  ]

constNothing :: String -> Maybe ()
constNothing = $$(runParserMocked empty [||empty||])

emptyTests :: TestTree
emptyTests = testGroup "empty should"
  [ testCase "fail the parser with no input" $ constNothing "" @?= Nothing
  , testCase "fail the parser with input" $ constNothing "a" @?= Nothing
  ]

digit :: String -> Maybe Char
digit = $$(runParserMocked Parsers.digit [||Parsers.digit||])

twoDigits :: String -> Maybe Char
twoDigits = $$(runParserMocked Parsers.twoDigits [||Parsers.twoDigits||])

satisfyTests :: TestTree
satisfyTests = testGroup "satisfy should"
  [ testCase "fail when given no input" $ digit "" @?= Nothing
  , testCase "fail when given incorrect input" $ digit "a" @?= Nothing
  , testCase "succeed when given correct input" $ digit "1" @?= Just '1'
  , testCase "actually consume input" $ twoDigits "1" @?= Nothing
  , testCase "consume more than 1 piece of input with two" $ twoDigits "12" @?= Just '2'
  ]

lookAheadTests :: TestTree
lookAheadTests = testGroup "lookAhead should" []

notFollowedByTests :: TestTree
notFollowedByTests = testGroup "notFollowedBy should" []

tryTests :: TestTree
tryTests = testGroup "try should" []

branchTests :: TestTree
branchTests = testGroup "branch should" []

conditionalTests :: TestTree
conditionalTests = testGroup "conditional should" []

manyAny :: String -> Maybe String
manyAny = $$(runParserMocked Parsers.recursive [||Parsers.recursive||])

recursionTests :: TestTree
recursionTests = testGroup "recursion should"
  [ testCase "work properly" $ manyAny "abc" @?= Just "abc"
  ]