{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables #-}
module Parsley.Applicative.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Applicative.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser)
import Parsley.Applicative (unit)

tests :: TestTree
tests = testGroup "Applicative" [ unitTests
                                , fmapTests
                                , voidTests
                                , thenTests
                                , prevTests
                                , liftA2Tests
                                , liftA3Tests
                                , sequenceTests
                                , betweenTests
                                ]

unit' :: String -> Maybe ()
unit' = $$(runParserMocked unit [||unit||])

unitTests :: TestTree
unitTests = testGroup "unit should"
  [ testCase "not need to consume input" $ unit' "" @?= Just ()
  , testCase "not fail if there is input" $ unit' "a" @?= Just ()
  ]

fmapTests :: TestTree
fmapTests = testGroup "fmap should" [] -- <$>/<&>

voidTests :: TestTree
voidTests = testGroup "void should" [] -- void

thenTests :: TestTree
thenTests = testGroup ">>/~> should" [] -- >>/~>

prevTests :: TestTree
prevTests = testGroup "<~ should" [] -- <~

liftA2Tests :: TestTree
liftA2Tests = testGroup "liftA2 should" [] -- <~>/<**>

liftA3Tests :: TestTree
liftA3Tests = testGroup "liftA3 should" [] -- liftA3

sequenceTests :: TestTree
sequenceTests = testGroup "sequence should" [] --traverse/repeat

betweenTests :: TestTree
betweenTests = testGroup "between should" [] --between