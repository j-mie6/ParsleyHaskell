{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables #-}
module Parsley.Combinator.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Combinator.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser, code)
import Parsley.Combinator (eof, more)

tests :: TestTree
tests = testGroup "Combinator" [ stringTests
                               , oneOfTests
                               , noneOfTests
                               , tokenTests
                               , eofTests
                               , moreTests
                               , charTests
                               , itemTests
                               , someTillTests
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

isNull :: String -> Maybe ()
isNull = $$(runParserMocked eof [||eof||])

eofTests :: TestTree
eofTests = testGroup "eof should"
  [ testCase "succeed on empty input" $ isNull "" @?= Just ()
  , testCase "fail on non-empty input" $ isNull "a" @?= Nothing
  ]

notNull :: String -> Maybe ()
notNull = $$(runParserMocked more [||more||])

moreTests :: TestTree
moreTests = testGroup "more should" []

charTests :: TestTree
charTests = testGroup "char should" []

itemTests :: TestTree
itemTests = testGroup "item should" []

someTillTests :: TestTree
someTillTests = testGroup "someTill should" []