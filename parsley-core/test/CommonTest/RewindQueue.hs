{-# LANGUAGE TypeApplications #-}
module CommonTest.RewindQueue where

import Test.Tasty (testGroup, TestTree)
import Test.Tasty.QuickCheck
  ( listOf,
    (===),
    (==>),
    conjoin,
    testProperty,
    forAll,
    elements,
    resize,
    Arbitrary(arbitrary),
    Property )
import CommonTest.Queue as QueueTest (genTests, QueueLike(..))

import Prelude hiding (null)
import Parsley.Internal.Common.RewindQueue.Impl (RewindQueue(..))
import qualified Parsley.Internal.Common.RewindQueue.Impl as Rewind

tests :: TestTree
tests = testGroup "RewindQueue" [
    testGroup "should behave like Queue" (QueueTest.genTests @RewindQueue),
    testProperty "rewind should reverse dequeue" rewindRoundtrip
  ]

rewindRoundtrip :: RewindQueue Integer -> Property
rewindRoundtrip rq = conjoin (map prop [0..size rq])
  where
    prop i = let rq' = iterate (snd . dequeue) rq !! i
             in toList (Rewind.rewind i rq') === toList rq

instance Arbitrary a => Arbitrary (RewindQueue a) where
  arbitrary = do undo <- listOf arbitrary
                 queue <- arbitrary
                 return $ RewindQueue queue undo (length undo)

instance QueueTest.QueueLike RewindQueue where
  empty = Rewind.empty
  null = Rewind.null
  size = Rewind.size
  enqueue = Rewind.enqueue
  dequeue = Rewind.dequeue
  enqueueAll = Rewind.enqueueAll
  toList = Rewind.toList
