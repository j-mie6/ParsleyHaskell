{-# LANGUAGE TemplateHaskell, UnboxedTuples #-}
module Parsley.Primitive.Test where
import Test.Tasty
import Test.Tasty.HUnit

import Prelude hiding (pure)
import Parsley (runParser, pure, code)
import Parsley.Applicative (unit)

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
pure7 = $$(runParser (pure (code 7)))

pureTests :: TestTree
pureTests = testGroup "pure should" [
    testCase "not need to consume input" (assertEqual "" (pure7 "") (Just 7)),
    testCase "not fail if there is input" (assertEqual "" (pure7 "a") (Just 7))
  ]

apTests :: TestTree
apTests = testGroup "<*> should" []

thenTests :: TestTree
thenTests = testGroup "*> should" []

prevTests :: TestTree
prevTests = testGroup "<* should" []

altTests :: TestTree
altTests = testGroup "<|> should" []

emptyTests :: TestTree
emptyTests = testGroup "empty should" []

satisfyTests :: TestTree
satisfyTests = testGroup "satisfy should" []

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