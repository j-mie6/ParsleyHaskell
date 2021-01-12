{-# LANGUAGE TemplateHaskell, UnboxedTuples #-}
module Parsley.Combinator.Test where
import Test.Tasty
import Test.Tasty.HUnit

import Prelude hiding ()
import Parsley (runParser, code)

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

oneOfTests :: TestTree
oneOfTests = testGroup "oneOf should" []

noneOfTests :: TestTree
noneOfTests = testGroup "noneOf should" []

tokenTests :: TestTree
tokenTests = testGroup "token should" []

eofTests :: TestTree
eofTests = testGroup "eof should" []

moreTests :: TestTree
moreTests = testGroup "more should" []

charTests :: TestTree
charTests = testGroup "char should" []

itemTests :: TestTree
itemTests = testGroup "item should" []

someTillTests :: TestTree
someTillTests = testGroup "someTill should" []