{-# LANGUAGE FlexibleInstances, AllowAmbiguousTypes, TypeApplications, RankNTypes, ScopedTypeVariables, ConstraintKinds #-}
module CommonTest.Queue where
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.HUnit ( testCase, (@?=) )
import Test.Tasty.QuickCheck
  ( listOf,
    (===),
    (==>),
    (.&&.),
    testProperty,
    Arbitrary(arbitrary),
    Property )

import Prelude hiding (null)
import Parsley.Internal.Common.QueueLike  (QueueLike(empty, null, size, enqueue, dequeue, enqueueAll))
import Parsley.Internal.Common.Queue ()
import Parsley.Internal.Common.Queue.Impl (Queue(..))
import qualified Parsley.Internal.Common.Queue.Impl as Queue

instance Arbitrary a => Arbitrary (Queue a) where
  arbitrary = do ins <- listOf arbitrary
                 outs <- listOf arbitrary
                 return $ Queue { ins = ins, insz = length ins
                                , outs = outs, outsz = length outs
                                }

class QueueLike q => QueueLikeImpl q where
  toList :: q a -> [a]

instance QueueLikeImpl Queue where
  toList = Queue.toList

type TestContext q = (Arbitrary (q Integer), QueueLikeImpl q, Show (q Integer))

tests :: TestTree
tests = testGroup "Queue" (genTests @Queue)

genTests :: forall q. TestContext q => [TestTree]
genTests = [ emptyTests @q
           , enqueueTests @q
           , testProperty "toList should roundtrip with enqueueAll" $ toListRound @q
           , dequeueTests @q
           ]

emptyTests :: forall q. TestContext q => TestTree
emptyTests = testGroup "empty should" [
    testCase "be null" $ null @q empty @?= True,
    testCase "have size 0" $ size @q empty @?= 0
  ]

enqueueTests :: forall q. TestContext q => TestTree
enqueueTests = testGroup "enqueue should" [
    testProperty "increase size by one" $ uncurry (enqueueSizeBy1 @q),
    testProperty "render empty non-null" $ flip (enqueueNonNull @q) empty,
    testProperty "render any other queue non-null" $ uncurry (enqueueNonNull @q),
    testProperty "behave like snoc" $ uncurry (enqueueIsSnoc @q),
    testProperty "serve as a model for enqueueAll" $ uncurry (enqueueAllModelsEnqueue @q)
  ]

enqueueSizeBy1 :: forall q. TestContext q => Integer -> q Integer -> Property
enqueueSizeBy1 x q = size q + 1 === size (enqueue x q)

enqueueNonNull :: forall q. TestContext q => Integer -> Queue Integer -> Bool
enqueueNonNull x = not . Queue.null . Queue.enqueue x

enqueueIsSnoc :: forall q. TestContext q => Integer -> Queue Integer -> Property
enqueueIsSnoc x q = Queue.toList q ++ [x] === Queue.toList (Queue.enqueue x q)

enqueueAllModelsEnqueue :: forall q. TestContext q => [Integer] -> Queue Integer -> Property
enqueueAllModelsEnqueue xs q = Queue.enqueueAll xs q === foldl (flip Queue.enqueue) q xs

dequeueTests :: forall q. TestContext q => TestTree
dequeueTests = testGroup "dequeue should" [
    testProperty "decrease size by one when non-empty" $ dequeueSizeBy1 @q,
    testProperty "behave like tail" $ dequeueIsTail @q
  ]

dequeueSizeBy1 :: forall q. TestContext q => Queue Integer -> Property
dequeueSizeBy1 q = not (Queue.null q) ==> Queue.size q === Queue.size (snd (Queue.dequeue q)) + 1

dequeueIsTail :: forall q. TestContext q => Queue Integer -> Property
dequeueIsTail q = not (Queue.null q) ==>
  let (x, q') = Queue.dequeue q
  in Queue.toList q === x : Queue.toList q'

toListRound :: forall q. TestContext q => [Integer] -> Property
toListRound xs = toList @q (enqueueAll xs empty) === xs
