module Main where

import Test.Tasty
import qualified CommonTest.Queue as QueueTest
import qualified CommonTest.RewindQueue as RewindQueueTest

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Common Tests" [ QueueTest.tests
                                 , RewindQueueTest.tests
                                 ]