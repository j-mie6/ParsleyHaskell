{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables #-}
module Parsley.Char.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Char.Parsers as Parsers

import Prelude hiding ((*>))
import Parsley ((*>))
import Parsley.Char (char, item)

tests :: TestTree
tests = testGroup "Char" [ stringTests
                         , oneOfTests
                         , noneOfTests
                         , tokenTests
                         , charTests
                         , itemTests
                         ]

stringTests :: TestTree
stringTests = testGroup "string should" []

nothing :: String -> Maybe Char
nothing = $$(runParserMocked Parsers.nothing [||Parsers.nothing||])

abc :: String -> Maybe Char
abc = $$(runParserMocked Parsers.abc [||Parsers.abc||])

oneOfTests :: TestTree
oneOfTests = testGroup "oneOf should"
  [ testCase "handle no options no input" $ nothing "" @?= Nothing
  , testCase "handle no options with input" $ nothing "a" @?= Nothing
  , testCase "parse any of characters" $ do
      abc "a" @?= Just 'a'
      abc "b" @?= Just 'b'
      abc "c" @?= Just 'c'
  , testCase "fail otherwise" $ abc "d" @?= Nothing
  ]

noneOfTests :: TestTree
noneOfTests = testGroup "noneOf should" []

tokenTests :: TestTree
tokenTests = testGroup "token should" []

charA :: String -> Maybe Char
charA = $$(runParserMocked (char 'a') [||char 'a'||])

charTests :: TestTree
charTests = testGroup "char should"
  [ testCase "fail on empty input" $ charA "" @?= Nothing
  , testCase "succeed on correct char" $ charA "a" @?= Just 'a'
  , testCase "fail on wrong char" $ charA "b" @?= Nothing
  ]

itemTests :: TestTree
itemTests = testGroup "item should" []
