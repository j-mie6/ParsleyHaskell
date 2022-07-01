module Main where

import Test.Tasty
import qualified Regression.Issue27 as Issue27

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Regression Tests" [ Issue27.tests
                                     ]
