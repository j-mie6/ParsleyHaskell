{-# LANGUAGE TypeApplications, StandaloneDeriving, DeriveGeneric, MonoLocalBinds #-}
module CommonTest.RangeSet where
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.HUnit ( testCase, (@?=) )
import Test.Tasty.QuickCheck
  ( listOf, chooseEnum,
    (===),
    (==>),
    (.&&.),
    property,
    testProperty,
    elements,
    forAll,
    genericShrink,
    Arbitrary(arbitrary, shrink),
    Property )

import Prelude hiding (null)

import Parsley.Internal.Common.RangeSet
import Data.List (nub, sort, intersect)
import GHC.Generics (Generic)

import Data.Word (Word8)

deriving instance Generic (RangeSet a)

data Digit = Zero | One | Two | Three | Four | Five | Six | Seven | Eight | Nine deriving (Ord, Eq, Enum, Bounded, Show, Generic)

instance (Arbitrary a, Enum a, Ord a) => Arbitrary (RangeSet a) where
  arbitrary = fmap fromList (listOf arbitrary)
  shrink = filter valid . genericShrink

instance Arbitrary Digit where
  arbitrary = chooseEnum (Zero, Nine)
  shrink n = [Zero .. pred n]

tests :: TestTree
tests = testGroup "RangeSet" [
    testProperty "arbitrary RangeSets should be valid" $ valid @Int,
    emptyTests,
    memberTests,
    insertTests,
    deleteTests,
    fromListTests,
    testProperty "elems and unelems shoudld be disjoint" $ elemUnelemDisjoint @Word8,
    testProperty "complement . complement = id" $ complementInverse @Digit,
    testProperty "unelems == elems . complement" $ complementElemsInverse @Digit,
    testProperty "findMin should find the minimum" $ findMinMinimum @Word,
    testProperty "findMax should find the maximum" $ findMaxMaximum @Int,
    testProperty "allLess should find everything strictly less than a value" $ allLessMin @Word,
    testProperty "allMore should find everything strictly more than a value" $ allMoreMax @Word,
    testProperty "union should union" $ uncurry (unionProperty @Int),
    testProperty "intersection should intersect" $ uncurry (intersectionProperty @Char),
    testProperty "difference should differentiate" $ uncurry (differenceProperty @Word)
  ]

emptyTests :: TestTree
emptyTests = testGroup "empty should" [
    testCase "be null" $ null empty @?= True,
    testCase "have size 0" $ size @Int empty @?= 0
  ]

-- member, notMember
memberTests :: TestTree
memberTests = testGroup "member should" [
    testCase "work when out of range" $ notMember 5 (fromRanges [(0, 4), (6, 9)]) @?= True,
    testCase "work when in range" $ member 5 (fromRanges [(0, 9)]) @?= True,
    testCase "work for exact" $ member 5 (fromRanges [(5, 5)]) @?= True,
    testProperty "perform like elem on elems" $ uncurry (memberElemProperty @Word)
  ]

-- insert
insertTests :: TestTree
insertTests =
  let t = fromList [6, 2, 7, 1, 5] -- 1-2, 5-7
  in testGroup "insert should" [
    testCase "add something in" $ member 3 (insert 3 t) @?= True,
    testCase "not affect membership for other items" $ member 4 (insert 3 t) @?= False,
    testCase "not remove membership" $ member 5 (insert 4 (insert 3 t)) @?= True
  ]

-- delete
deleteTests :: TestTree
deleteTests =
  let t = fromList [6, 2, 7, 1, 5] -- 1-2, 5-7
  in testGroup "delete should" [
    testCase "remove an element" $ notMember 2 (delete 2 t) @?= True,
    testCase "not affect membership for other items" $ member 1 (delete 2 t) @?= True,
    testCase "produce valid trees" $ all valid (scanr delete t (sort (elems t))) @?= True
  ]

fromListTests :: TestTree
fromListTests = testGroup "fromList" [
    testProperty "should compose with elems to form (sort . nub)" $ nubSortProperty @Int,
    testProperty "specifically, case 1" $ nubSortProperty [2,0,3,4,2,6],
    testProperty "specifically, case 2" $ nubSortProperty [6,7,4,0,6,10,2,12,8]
  ]

findMinMinimum :: (Ord a, Show a, Enum a) => RangeSet a -> Property
findMinMinimum t = findMin t === safeMinimum (elems t)
  where
    safeMinimum [] = Nothing
    safeMinimum xs = Just $ minimum xs

findMaxMaximum :: (Ord a, Show a, Enum a) => RangeSet a -> Property
findMaxMaximum t = findMax t === safeMaximum (elems t)
  where
    safeMaximum [] = Nothing
    safeMaximum xs = Just $ maximum xs

nubSortProperty :: (Enum a, Ord a, Show a) => [a] -> Property
nubSortProperty xs = sort (nub xs) === elems (fromList xs)

memberElemProperty :: (Enum a, Ord a, Show a) => a -> RangeSet a -> Property
memberElemProperty x t = member x t === elem x (elems t)

elemUnelemDisjoint :: (Enum a, Bounded a, Eq a, Show a) => RangeSet a -> Property
elemUnelemDisjoint t = intersect (elems t) (unelems t) === []

complementInverse :: (Enum a, Bounded a, Ord a, Show a) => RangeSet a -> Property
complementInverse t = elems (complement (complement t)) === elems t

complementElemsInverse :: (Enum a, Bounded a, Ord a, Show a) => RangeSet a -> Property
complementElemsInverse t = unelems t === elems (complement t)

unionProperty :: (Ord a, Enum a, Show a) => RangeSet a -> RangeSet a -> Property
unionProperty t1 t2 = not (null t1 && null t2) ==>
  forAll (elements (elems t1 ++ elems t2)) (\x ->
         member x (t1 `union` t2))
  .&&. valid (t1 `union` t2)

intersectionProperty :: (Ord a, Enum a, Show a) => RangeSet a -> RangeSet a -> Property
intersectionProperty t1 t2 = not (null t1 && null t2) ==>
  forAll (elements (elems t1 ++ elems t2)) (\x ->
         (member x t1 && member x t2) === member x (t1 `intersection` t2))
  .&&. valid (t1 `intersection` t2)

differenceProperty :: (Ord a, Enum a, Show a) => RangeSet a -> RangeSet a -> Property
differenceProperty t1 t2 = not (null t1 && null t2) ==>
  forAll (elements (elems t1 ++ elems t2)) (\x ->
         (member x t1 && not (member x t2)) === member x (t1 `difference` t2))
  .&&. valid (t1 `difference` t2)

allLessMin :: (Ord a, Enum a, Show a) => RangeSet a -> a -> Property
allLessMin t x = allLess x t === fromList (filter (< x) (elems t))

allMoreMax :: (Ord a, Enum a, Show a) => RangeSet a -> a -> Property
allMoreMax t x = allMore x t === fromList (filter (> x) (elems t))

{-
    fromRanges, insertRange
-}