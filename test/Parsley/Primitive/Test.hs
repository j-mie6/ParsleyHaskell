{-# LANGUAGE TemplateHaskell, UnboxedTuples #-}
module Parsley.Primitive.Test where
import Test.Tasty
import Test.Tasty.HUnit
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
                              ]

pure7 :: String -> Maybe Int
pure7 = $$(runParser Parsers.pure7)

pureTests :: TestTree
pureTests = testGroup "pure should"
  [ testCase "not need to consume input" (assertEqual "" (pure7 "") (Just 7))
  , testCase "not fail if there is input" (assertEqual "" (pure7 "a") (Just 7))
  ]

apTests :: TestTree
apTests = testGroup "<*> should" []

thenTests :: TestTree
thenTests = testGroup "*> should" []

prevTests :: TestTree
prevTests = testGroup "<* should" []

altTests :: TestTree
altTests = testGroup "<|> should" []

constNothing :: String -> Maybe ()
constNothing = $$(runParser empty)

emptyTests :: TestTree
emptyTests = testGroup "empty should"
  [ testCase "fail the parser with no input" (assertEqual "" (constNothing "") Nothing)
  , testCase "fail the parser with input" (assertEqual "" (constNothing "a") Nothing)
  ]

digit :: String -> Maybe Char
digit = $$(runParser Parsers.digit)

twoDigits :: String -> Maybe Char
twoDigits = $$(runParser Parsers.twoDigits)

satisfyTests :: TestTree
satisfyTests = testGroup "satisfy should"
  [ testCase "fail when given no input" (assertEqual "" (digit "") Nothing)
  , testCase "fail when given incorrect input" (assertEqual "" (digit "a") Nothing)
  , testCase "succeed when given correct input" (assertEqual "" (digit "1") (Just '1'))
  , testCase "actually consume input" (assertEqual "" (twoDigits "1") (Nothing))
  , testCase "consume more than 1 piece of input with two" (assertEqual "" (twoDigits "12") (Just '2'))
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