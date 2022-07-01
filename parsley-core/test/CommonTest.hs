module Main where

import Test.Tasty
import qualified CommonTest.Queue as QueueTest
import qualified CommonTest.RewindQueue as RewindQueueTest
import qualified CommonTest.RangeSet as RangeSetTest

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Common Tests" [ QueueTest.tests
                                 , RewindQueueTest.tests
                                 , RangeSetTest.tests
                                 ]
