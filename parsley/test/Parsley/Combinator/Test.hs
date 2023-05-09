{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Parsley.Combinator.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Combinator.Parsers as Parsers

import Prelude hiding ((*>))
import Parsley ((*>))
import Parsley.Combinator (eof, more)
import Parsley.Char       (char)

tests :: TestTree
tests = testGroup "Combinator" [ eofTests
                               , moreTests
                               , someTillTests
                               , factoringTests
                               ]

isNull :: String -> Maybe ()
isNull = $$(runParserMocked eof [||eof||])

eofTests :: TestTree
eofTests = testGroup "eof should"
  [ testCase "succeed on empty input" $ isNull "" @?= Just ()
  , testCase "fail on non-empty input" $ isNull "a" @?= Nothing
  ]

notNull :: String -> Maybe ()
notNull = $$(runParserMocked more [||more||])

notNullThenA :: String -> Maybe Char
notNullThenA = $$(runParserMocked (more *> char 'a') [||more *> char 'a'||])

moreTests :: TestTree
moreTests = testGroup "more should"
  [ testCase "fail on empty input" $ notNull "" @?= Nothing
  , testCase "succeed on non-empty input" $ notNull "a" @?= Just ()
  , testCase "not consume input" $ notNullThenA "a" @?= Just 'a'
  ]

someTillTests :: TestTree
someTillTests = testGroup "someTill should" []

factoring :: String -> Maybe [String]
factoring = $$(runParserMocked Parsers.factoring [||Parsers.factoring||])

factoringTests :: TestTree
factoringTests = testGroup "factoring should"
  [ testCase "succeed on input" $ factoring "" @?= Just []
  , testCase "succeed on input" $ factoring "if" @?= Just ["if"]
  , testCase "succeed on input" $ factoring "continue" @?= Just ["continue"]
  , testCase "succeed on input" $ factoring "hello!" @?= Just ["hello!"]
  , testCase "succeed on input" $ factoring "while." @?= Just ["while"]
  , testCase "succeed on input" $ factoring "coodbye" @?= Nothing
  ]
