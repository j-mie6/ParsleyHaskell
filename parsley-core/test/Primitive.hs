{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
-- {-# OPTIONS_GHC -ddump-splices #-}
module Main where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Primitive.Parsers as Parsers

import Parsley.Internal (empty, line, col)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Primitive Combinator Tests" [ pureTests
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
                                               , positionTests
                                               ]

pure7 :: String -> Maybe Int
pure7 = $$(parseMocked Parsers.pure7 [||Parsers.pure7||])

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
abOrC = $$(parseMocked Parsers.abOrC [||Parsers.abOrC||])

abOrCThenD :: String -> Maybe String
abOrCThenD = $$(parseMocked Parsers.abOrCThenD [||Parsers.abOrCThenD||])

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
constNothing = $$(parseMocked empty [||empty||])

emptyTests :: TestTree
emptyTests = testGroup "empty should"
  [ testCase "fail the parser with no input" $ constNothing "" @?= Nothing
  , testCase "fail the parser with input" $ constNothing "a" @?= Nothing
  ]

digit :: String -> Maybe Char
digit = $$(parseMocked Parsers.digit [||Parsers.digit||])

twoDigits :: String -> Maybe Char
twoDigits = $$(parseMocked Parsers.twoDigits [||Parsers.twoDigits||])

satisfyTests :: TestTree
satisfyTests = testGroup "satisfy should"
  [ testCase "fail when given no input" $ digit "" @?= Nothing
  , testCase "fail when given incorrect input" $ digit "a" @?= Nothing
  , testCase "succeed when given correct input" $ digit "1" @?= Just '1'
  , testCase "actually consume input" $ twoDigits "1" @?= Nothing
  , testCase "consume more than 1 piece of input with two" $ twoDigits "12" @?= Just '2'
  ]

lookAheadDigit :: String -> Maybe Char
lookAheadDigit = $$(parseMocked Parsers.lookAheadDigit [||Parsers.lookAheadDigit||])

lookAheadTests :: TestTree
lookAheadTests = testGroup "lookAhead should"
  [ testCase "rollback consumed input" $ lookAheadDigit "9" @?= Just '9'
  , testCase "fail when given no input when expected" $ lookAheadDigit "" @?= Nothing
  ]

notFollowedByTests :: TestTree
notFollowedByTests = testGroup "notFollowedBy should" []

tryTests :: TestTree
tryTests = testGroup "try should" []

branchTests :: TestTree
branchTests = testGroup "branch should" []

conditionalTests :: TestTree
conditionalTests = testGroup "conditional should" []

manyAny :: String -> Maybe String
manyAny = $$(parseMocked Parsers.recursive [||Parsers.recursive||])

recursionTests :: TestTree
recursionTests = testGroup "recursion should"
  [ testCase "work properly" $ manyAny "abc" @?= Just "abc"
  ]

lineStarts1 :: String -> Maybe Int
lineStarts1 = $$(parseMocked line [||line||])

columnStarts1 :: String -> Maybe Int
columnStarts1 = $$(parseMocked col [||col||])

posAfterA :: String -> Maybe (Int, Int)
posAfterA = $$(parseMocked Parsers.posAfterA  [||Parsers.posAfterA||])

posAfterNewline :: String -> Maybe ((Int, Int), (Int, Int))
posAfterNewline = $$(parseMocked Parsers.posAfterNewline  [||Parsers.posAfterNewline||])

posAfterTab :: String -> Maybe ((Int, Int), (Int, Int))
posAfterTab = $$(parseMocked Parsers.posAfterTab  [||Parsers.posAfterTab||])

posAfterLookahead :: String -> Maybe ((Int, Int), (Int, Int))
posAfterLookahead = $$(parseMocked Parsers.posAfterLookahead [||Parsers.posAfterLookahead||])

posAfterNotFollowedBy :: String -> Maybe ((Int, Int), (Int, Int))
posAfterNotFollowedBy = $$(parseMocked Parsers.posAfterNotFollowedBy [||Parsers.posAfterNotFollowedBy||])

positionTests :: TestTree
positionTests = testGroup "position combinators should"
  [ testCase "start at line 1" $ lineStarts1 "" @?= Just 1
  , testCase "start at column 1" $ columnStarts1 "" @?= Just 1
  , testCase "advance by 1 column only after regular character" $ posAfterA "a" @?= Just (1, 2)
  , testCase "advance by 1 line and reset column after newline" $ posAfterNewline "a\n\n" @?= Just ((2, 1), (3, 1))
  , testCase "advance to nearest tab boundary on tab" $ posAfterTab "\ta\t" @?= Just ((1, 5), (1, 9))
  , testCase "work with lookahead" $ posAfterLookahead "\t" @?= Just ((1, 1), (1, 5))
  , testCase "work with notFollowedBy" $ posAfterNotFollowedBy "\n" @?= Just ((1, 1), (2, 1))
  ]
