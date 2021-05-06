{-# LANGUAGE TemplateHaskell, UnboxedTuples, ScopedTypeVariables, TypeApplications #-}
module Parsley.Register.Test where
import Test.Tasty
import Test.Tasty.HUnit
import TestUtils
import qualified Parsley.Register.Parsers as Parsers

import Prelude hiding ()
import Parsley (runParser)

-- NewRegister is required for any test and can only be tested with another component
-- so it is omitted
tests :: TestTree
tests = testGroup "Register" [ getTests
                             , putTests
                             , getsTests
                             , modifyTests
                             , moveTests
                             , swapTests
                             , localTests
                             , bindTests
                             , rollbackTests
                             , forTests
                             ]

getPure :: String -> Maybe Int
getPure = $$(runParserMocked Parsers.getPure [||Parsers.getPure||])

getPersists :: String -> Maybe Int
getPersists = $$(runParserMocked Parsers.getPersists [||Parsers.getPersists||])

getPersistsBranch :: String -> Maybe Int
getPersistsBranch = $$(runParserMocked Parsers.getPersistsBranch [||Parsers.getPersistsBranch||])

getNoInput :: String -> Maybe Int
getNoInput = $$(runParserMocked Parsers.getNoInput [||Parsers.getNoInput||])

getTests :: TestTree
getTests = testGroup "get should"
  [ testCase "work when given no input" $ getPure "" @?= Just 8
  , testCase "work when given input" $ getPure "a" @?= Just 8
  , testCase "persist across other parsers" $ getPersists "a" @?= Just 8
  , testCase "persist across branches" $ do
      getPersistsBranch "" @?= Just 8
      getPersistsBranch "a" @?= Just 8
  , testCase "not consume input" $ getNoInput "a" @?= Just 8
  ]

putPure :: String -> Maybe Int
putPure = $$(runParserMocked Parsers.putPure [||Parsers.putPure||])

putSeq :: String -> Maybe Char
putSeq = $$(runParserMocked Parsers.putSeq [||Parsers.putSeq||])

putPut :: String -> Maybe Int
putPut = $$(runParserMocked Parsers.putPut [||Parsers.putPut||])

putCarries :: String -> Maybe Bool
putCarries = $$(runParserMocked Parsers.putCarries [||Parsers.putCarries||])

putTests :: TestTree
putTests = testGroup "put should"
  [ testCase "work when given no input" $ putPure "" @?= Just 7
  , testCase "work when given input" $ putPure "a" @?= Just 7
  , testCase "ensure the sub-parser is ran first" $ putSeq "b" @?= Just 'b'
  , testCase "puts should override puts" $ putPut "" @?= Just 6
  , testCase "put should carry over in branches" $ do
      putCarries "" @?= Just True
      putCarries "a" @?= Just False
  ]

getsTests :: TestTree
getsTests = testGroup "gets should" [] -- gets_

modifyTests :: TestTree
modifyTests = testGroup "modify should" [] -- modify_

moveTests :: TestTree
moveTests = testGroup "move should" []

swapTests :: TestTree
swapTests = testGroup "swap should" []

localTests :: TestTree
localTests = testGroup "local should" []

bindTests :: TestTree
bindTests = testGroup "bind should" []

rollbackTests :: TestTree
rollbackTests = testGroup "rollback should" []

forTests :: TestTree
forTests = testGroup "for should" []