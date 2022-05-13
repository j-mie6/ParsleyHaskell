{-# LANGUAGE DerivingStrategies, MagicHash, UnboxedTuples, RoleAnnotations, TypeApplications, MultiWayIf #-}
{-# OPTIONS_HADDOCK prune #-}
{-|
Module      : Parsley.Internal.Common.RangeSet
Description : Efficient set for contiguous data.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the implementation of an efficient set for contiguous data. It has a much
smaller memory footprint than a @Set@, and can result in asymptotically faster operations.

@since 2.1.0.0
-}
module Parsley.Internal.Common.RangeSet (
    RangeSet(..),
    empty, singleton, null, full, isSingle, extractSingle, size, sizeRanges,
    member, notMember, findMin, findMax,
    insert, delete,
    union, intersection, difference, disjoint, complement,
    isSubsetOf, isProperSubsetOf,
    allLess, allMore,
    elems, unelems, fromRanges, insertRange, fromList,
    fold,
    -- Testing
    valid
  ) where

import Prelude hiding (null)
import Control.Applicative (liftA2)

import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

{-# INLINE diff #-}
diff :: Enum a => a -> a -> Size
diff !l !u = fromEnum u - fromEnum l + 1

type Size = Int
{-|
A @Set@ type designed for types that are `Enum` as well as `Ord`. This allows the `RangeSet` to
compress the data when it is contiguous, reducing memory-footprint and enabling otherwise impractical
operations like `complement` for `Bounded` types.

@since 2.1.0.0
-}
data RangeSet a = Fork {-# UNPACK #-} !Int {-# UNPACK #-} !Size !a !a !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock Show
type role RangeSet nominal

{-|
The empty `RangeSet`.

@since 2.1.0.0
-}
{-# INLINE empty #-}
empty :: RangeSet a
empty = Tip

{-|
A `RangeSet` containing a single value.

@since 2.1.0.0
-}
singleton :: a -> RangeSet a
singleton x = single 1 x x

{-# INLINE fork #-}
fork :: Enum a => a -> a -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = forkSz (size lt + size rt + diff l u) l u lt rt

forkSz :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
forkSz !sz !l !u !lt !rt = Fork (max (height lt) (height rt) + 1) sz l u lt rt

{-# INLINE single #-}
single :: Size -> a -> a -> RangeSet a
single !sz !l !u = Fork 1 sz l u Tip Tip

{-|
Is this set empty?

@since 2.1.0.0
-}
null :: RangeSet a -> Bool
null Tip = True
null _ = False

{-|
Is this set full?

@since 2.1.0.0
-}
full :: (Eq a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ _ l u _ _) = l == minBound && maxBound == u

{-|
Does this set contain a single element?

@since 2.1.0.0
-}
isSingle :: RangeSet a -> Bool
isSingle (Fork _ 1 _ _ _ _) = True
isSingle _ = False

{-|
Possibly extract the element contained in the set if it is a singleton set.

@since 2.1.0.0
-}
extractSingle :: Eq a => RangeSet a -> Maybe a
extractSingle (Fork _ _ x y Tip Tip) | x == y = Just x
extractSingle _                               = Nothing

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _ _) = h

{-|
Return the number of /elements/ in the set.

@since 2.1.0.0
-}
{-# INLINE size #-}
size :: RangeSet a -> Int
size Tip = 0
size (Fork _ sz _ _ _ _) = sz

{-|
Return the number of /contiguous ranges/ that populate the set.

@since 2.1.0.0
-}
sizeRanges :: RangeSet a -> Int
sizeRanges = fold (\_ _ szl szr -> szl + szr + 1) 0

{-|
Test whether or not a given value is found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE member #-}
member :: forall a. Ord a => a -> RangeSet a -> Bool
member !x = go
  where
    go (Fork _ _ l u lt rt)
      | l <= x    = x <= u || go rt
      | otherwise = go lt
    go Tip = False

{-|
Test whether or not a given value is not found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE notMember #-}
notMember :: Ord a => a -> RangeSet a -> Bool
notMember x = not . member x

{-# INLINE ifeq #-}
ifeq :: RangeSet a -> RangeSet a -> RangeSet a -> (RangeSet a -> RangeSet a) -> RangeSet a
ifeq !x !x' y f = if size x == size x' then y else f x'

{-|
Insert a new element into the set.

@since 2.1.0.0
-}
{-# INLINEABLE insert #-}
insert :: forall a. (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
insert !x Tip = single 1 x x
insert x t@(Fork h sz l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x = if
    | x <= u -> t
  -- If it is adjacent to the upper range, it may fuse
    | x == succ u -> fuseRight h (sz + 1) l x lt rt                                -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
    | otherwise -> ifeq rt (insert x rt) t (balance (sz + 1) l u lt)               -- cannot be biased, because fusion can shrink a tree
  | {- x < l -} otherwise = if
  -- If it is adjacent to the lower, it may fuse
    x == pred l then fuseLeft h (sz + 1) x u lt rt                                 -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
                else ifeq lt (insert x lt) t $ \lt' -> balance (sz + 1) l u lt' rt -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !h !sz !x !u Tip !rt = Fork h sz x u lt rt
    fuseLeft h sz x u (Fork _ lsz ll lu llt lrt) rt
      | (# !l, !x', lt' #) <- maxDelete lsz ll lu llt lrt
      -- we know there exists an element larger than x'
      -- if x == x' + 1, we fuse (x != x' since that breaks disjointness, x == pred l)
      , x == succ x' = balanceR sz l u lt' rt
      | otherwise    = Fork h sz x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !h !sz !l !x !lt Tip = Fork h sz l x lt rt
    fuseRight h sz l x lt (Fork _ rsz rl ru rlt rrt)
      | (# !x', !u, rt' #) <- minDelete rsz rl ru rlt rrt
      -- we know there exists an element smaller than x'
      -- if x == x' - 1, we fuse (x != x' since that breaks disjointness, as x == succ u)
      , x == pred x' = balanceL sz l u lt rt'
      | otherwise    = Fork h sz l x lt rt

{-|
Remove an element from the set, if it appears.

@since 2.1.0.0
-}
{-# INLINEABLE delete #-}
delete :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
delete !_ Tip = Tip
delete x t@(Fork h sz l u lt rt) =
  case compare l x of
    -- If its the only part of the range, the node is removed
    EQ | x == u    -> glue (sz - 1) lt rt
    -- If it's at an extreme, it shrinks the range
       | otherwise -> Fork h (sz - 1) (succ l) u lt rt
    LT -> case compare x u of
    -- If it's at an extreme, it shrinks the range
       EQ          -> Fork h (sz - 1) l (pred u) lt rt
    -- Otherwise, if it's still in range, the range undergoes fission
       LT          -> fission (sz - 1) l x u lt rt
    -- Otherwise delete and balance for one of the left or right
       GT          -> ifeq rt (delete x rt) t $ balance (sz - 1) l u lt             -- cannot be biased, because fisson can grow a tree
    GT             -> ifeq lt (delete x lt) t $ \lt' -> balance (sz - 1) l u lt' rt -- cannot be biased, because fisson can grow a tree
  where
    {- Fission breaks a node into two new ranges
       we'll push the range down into the right arbitrarily
       To do this, we have to make it a child of the right-tree's left most position. -}
    {-# INLINE fission #-}
    fission !sz !l1 !x !u2 !lt !rt =
      let u1 = pred x
          l2 = succ x
          rt' = unsafeInsertL (diff l2 u2) l2 u2 rt
      in balanceR sz l1 u1 lt rt'

{-|
Inserts an range at the left-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertL #-}
unsafeInsertL :: Size -> a -> a -> RangeSet a -> RangeSet a
unsafeInsertL !newSz l u Tip = single newSz l u
unsafeInsertL newSz l u (Fork _ sz l' u' lt rt) = balanceL (sz + newSz) l' u' (unsafeInsertL newSz l u lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: Size -> a -> a -> RangeSet a -> RangeSet a
unsafeInsertR !newSz l u Tip = single newSz l u
unsafeInsertR newSz l u (Fork _ sz l' u' lt rt) = balanceR (sz + newSz) l' u' lt (unsafeInsertR newSz l u rt)

{-|
This deletes the left-most range of the tree.
-}
{-# INLINEABLE deleteLeftmost #-}
deleteLeftmost :: Size -> Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
deleteLeftmost !_ !_ !_ !_ Tip rt = rt
deleteLeftmost szRemoved sz l u (Fork _ szl ll lu llt lrt) rt =
  balanceR (sz - szRemoved) l u (deleteLeftmost szRemoved szl ll lu llt lrt) rt

{-|
This deletes the right-most range of the tree.
It *must not* be used with an empty tree.
-}
{-{-# INLINEABLE unsafeDeleteR #-}
unsafeDeleteR :: Int -> RangeSet a -> RangeSet a
unsafeDeleteR !_ (Fork _ _ _ _ lt Tip) = lt
unsafeDeleteR szRemoved (Fork _ sz l u lt rt) = balanceL (sz - szRemoved) l u lt (unsafeDeleteR szRemoved rt)
unsafeDeleteR _ _ = error "unsafeDeleteR called on empty tree"-}

{-|
Find the minimum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMin #-}
findMin :: RangeSet a -> Maybe a
findMin Tip = Nothing
findMin (Fork _ _ l u lt _) = let (# !m, !_ #) = minRange l u lt in Just m

{-# INLINEABLE minRange #-}
minRange :: a -> a -> RangeSet a -> (# a, a #)
minRange !l !u Tip                 = (# l, u #)
minRange _  _  (Fork _ _ l u lt _) = minRange l u lt

{-|
Find the maximum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMax #-}
findMax :: RangeSet a -> Maybe a
findMax Tip = Nothing
findMax (Fork _ _ l u _ rt) = let (# !_, !m #) = maxRange l u rt in Just m

{-# INLINEABLE maxRange #-}
maxRange :: a -> a -> RangeSet a -> (# a, a #)
maxRange !l !u Tip                 = (# l, u #)
maxRange _  _  (Fork _ _ l u _ rt) = maxRange l u rt

{-# INLINE minDelete #-}
minDelete :: Size -> a -> a -> RangeSet a -> RangeSet a -> (# a, a, RangeSet a #)
minDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go !sz !l !u Tip !rt = (# l, u, sz - size rt, rt #)
    go sz l u (Fork _ lsz ll lu llt lrt) rt =
      let (# !ml, !mu, !msz, lt' #) = go lsz ll lu llt lrt
      in (# ml, mu, msz, balanceR (sz - msz) l u lt' rt #)

{-# INLINE maxDelete #-}
maxDelete :: Size -> a -> a -> RangeSet a -> RangeSet a -> (# a, a, RangeSet a #)
maxDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go !sz !l !u !lt Tip = (# l, u, sz - size lt, lt #)
    go sz l u lt (Fork _ rsz rl ru rlt rrt) =
      let (# !ml, !mu, !msz, rt' #) = go rsz rl ru rlt rrt
      in (# ml, mu, msz, balanceL (sz - msz) l u lt rt' #)

{-# INLINABLE balance #-}
balance :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
balance !sz !l !u lt rt
  | height lt > height rt + 1 = balanceL sz l u lt rt
  | height rt > height lt + 1 = balanceR sz l u lt rt
  | otherwise = forkSz sz l u lt rt

{-# NOINLINE balanceL #-}
balanceL :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !sz !l1 !u1 lt@(Fork !hlt !szl !l2 !u2 !llt !rlt) !rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkSz sz l1 u1 lt rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hrlt = rotr sz l1 u1 lt rt
  | otherwise    = rotr sz l1 u1 (rotl szl l2 u2 llt rlt) rt
  where
    !dltrt = hlt - height rt
    !hllt = height llt
    !hrlt = height rlt
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL sz l u Tip rt | height rt <= 1 = forkSz sz l u Tip rt
balanceL _ _ _ Tip _ = error "Right should have shrank, but is still 1 taller than a Tip!"

{-# NOINLINE balanceR #-}
balanceR :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR !sz !l1 !u1 !lt rt@(Fork !hrt szr l2 u2 lrt rrt)
  -- both sides are equal height or off by one
  | drtlt <= 1 = forkSz sz l1 u1 lt rt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hlrt = rotl sz l1 u1 lt rt
  | otherwise    = rotl sz l1 u1 lt (rotr szr l2 u2 lrt rrt)
  where
    !drtlt = hrt - height lt
    !hlrt = height lrt
    !hrrt = height rrt
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR sz l u lt Tip | height lt <= 1 = forkSz sz l u lt Tip
balanceR _ _ _ _ Tip = error "Left should have shrank, but is still 1 taller than a Tip!"

{-# INLINE rotr #-}
rotr :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotr !sz !l1 !u1 (Fork _ szl l2 u2 p q) !r = forkSz sz l2 u2 p (forkSz (sz - szl + size q) l1 u1 q r)
rotr _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotl !sz !l1 !u1 !p (Fork _ szr l2 u2 q r) = forkSz sz l2 u2 (forkSz (sz - szr + size q) l1 u1 p q) r
rotl _ _ _ _ _ = error "rotr on Tip"

{-|
Unions two sets together such that if and only if an element appears in either one of the sets, it
will appear in the result set.

@since 2.1.0.0
-}
{-# INLINABLE union #-}
union :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
union t Tip = t
union Tip t = t
union t@(Fork _ _ l u lt rt) t' = case split l u t' of
  (# lt', rt' #)
    | ltlt' `ptrEq` lt, rtrt' `ptrEq` rt -> t
    | otherwise                          -> link l u ltlt' rtrt'
    where !ltlt' = lt `union` lt'
          !rtrt' = rt `union` rt'

{-|
Intersects two sets such that an element appears in the result if and only if it is present in both
of the provided sets.

@since 2.1.0.0
-}
{-# INLINABLE intersection #-}
intersection :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Fork _ _ l1 u1 lt1 rt1) t2 =
  case overlap of
    Tip -> unsafeMerge lt1lt2 rt1rt2
    Fork 1 sz x y _ _
      | x == l1, y == u1
      , lt1lt2 `ptrEq` lt1, rt1rt2 `ptrEq` rt1 -> t1
      | otherwise -> unsafeLink sz x y lt1lt2 rt1rt2
    Fork _ sz x y lt' rt' -> unsafeLink (sz - size lt' - size rt') x y (unsafeMerge lt1lt2 lt') (unsafeMerge rt' rt1rt2)
  where
    (# !lt2, !overlap, !rt2 #) = splitOverlap l1 u1 t2
    !lt1lt2 = intersection lt1 lt2
    !rt1rt2 = intersection rt1 rt2

{-|
Do two sets have no elements in common?

@since 2.1.0.0
-}
{-# INLINE disjoint #-}
disjoint :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
disjoint Tip _ = True
disjoint _ Tip = True
disjoint (Fork _ _ l u lt rt) t = case splitOverlap l u t of
  (# lt', Tip, rt' #) -> disjoint lt lt' && disjoint rt rt'
  _                   -> False

{-|
Removes all elements from the first set that are found in the second set.

@since 2.1.0.0
-}
{-# INLINEABLE difference #-}
difference :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
difference Tip _ = Tip
difference t Tip = t
difference t (Fork _ _ l u lt rt) = case split l u t of
  (# lt', rt' #)
    | size lt'lt + size rt'rt == size t -> t
    | otherwise -> unsafeMerge lt'lt rt'rt
    where
      !lt'lt = difference lt' lt
      !rt'rt = difference rt' rt

{-# INLINEABLE insertLAdj #-}
insertLAdj :: (Enum a, Eq a) => Size -> a -> a -> Int -> Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
insertLAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case minRange tl tu tlt of
  (# !l', _ #) | l' == succ u -> fuseL newSz l th tsz tl tu tlt trt
               | otherwise    -> balanceL (tsz + newSz) tl tu (unsafeInsertL newSz l u tlt) trt --unsafeInsertL newSz l u t
  where
    {-# INLINEABLE fuseL #-}
    fuseL :: Size -> a -> Int -> Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
    fuseL !newSz !l' !h !sz !l !u lt rt = case lt of
      Tip -> Fork h (newSz + sz) l' u Tip rt
      Fork lh lsz ll lu llt lrt  -> Fork h (newSz + sz) l u (fuseL newSz l' lh lsz ll lu llt lrt) rt

{-# INLINEABLE insertRAdj #-}
insertRAdj :: (Enum a, Eq a) => Size -> a -> a -> Int -> Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
insertRAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case maxRange tl tu trt of
  (# _, !u' #) | u' == pred l -> fuseR newSz u th tsz tl tu tlt trt
               | otherwise    -> balanceR (tsz + newSz) tl tu tlt (unsafeInsertR newSz l u trt) --unsafeInsertR newSz l u t
  where
    {-# INLINEABLE fuseR #-}
    fuseR :: Size -> a -> Int -> Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
    fuseR !newSz !u' !h !sz !l !u lt rt = case rt of
      Tip -> Fork h (newSz + sz) l u' lt Tip
      Fork rh rsz rl ru rlt rrt  -> Fork h (newSz + sz) l u lt (fuseR newSz u' rh rsz rl ru rlt rrt)

{-# INLINABLE link #-}
link :: (Enum a, Eq a) => a -> a -> RangeSet a -> RangeSet a -> RangeSet a
link !l !u Tip Tip = single (diff l u) l u
link l u Tip (Fork rh rsz rl ru rlt rrt) = insertLAdj (diff l u) l u rh rsz rl ru rlt rrt
link l u (Fork lh lsz ll lu llt lrt) Tip = insertRAdj (diff l u) l u lh lsz ll lu llt lrt
link l u lt@(Fork _ lsz ll lu llt lrt) rt@(Fork _ rsz rl ru rlt rrt) =
  unsafeLink (diff l' u') l' u' lt'' rt''
  where
    -- we have to check for fusion up front
    (# !lmaxl, !lmaxu, lt' #) = maxDelete lsz ll lu llt lrt
    (# !rminl, !rminu, rt' #) = minDelete rsz rl ru rlt rrt

    (# !l', !lt'' #) | lmaxu == pred l = (# lmaxl, lt' #)
                     | otherwise       = (# l, lt #)

    (# !u', !rt'' #) | rminl == succ u = (# rminu, rt' #)
                     | otherwise       = (# u, rt #)

{-# INLINEABLE unsafeLink #-}
unsafeLink :: Size -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
unsafeLink !newSz !l !u Tip rt = unsafeInsertL newSz l u rt
unsafeLink newSz l u lt Tip = unsafeInsertR newSz l u lt
unsafeLink newSz l u lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (newSz + szl + szr) rl ru (unsafeLink newSz l u lt rlt) rrt
  | hr < hl + 1 = balanceR (newSz + szl + szr) ll lu llt (unsafeLink newSz l u lrt rt)
  | otherwise   = forkSz (newSz + szl + szr) l u lt rt

-- This version checks for fusion between the two trees to be merged
{-{-# INLINEABLE merge #-}
merge :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
merge Tip Tip = Tip
merge t Tip = t
merge Tip t = t
merge t1 t2 =
  let (# !_, !u1 #) = unsafeMaxRange t1
      (# !l2, !u2, t2' #) = unsafeMinDelete t2
  in if succ u1 == l2 then unsafeMerge (unsafeFuseR (diff l2 u2) u2 t1) t2'
     else unsafeMerge t1 t2-}

-- This assumes that the trees are /totally/ disjoint
{-# INLINEABLE unsafeMerge #-}
unsafeMerge :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
unsafeMerge Tip rt = rt
unsafeMerge lt Tip = lt
unsafeMerge lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (szl + szr) rl ru (unsafeMerge lt rlt) rrt
  | hr < hl + 1 = balanceR (szl + szr) ll lu llt (unsafeMerge lrt rt)
  | otherwise   = glue (szl + szr) lt rt

-- Trees must be balanced with respect to eachother, since we pull from the tallest, no balancing is required
{-# INLINEABLE glue #-}
glue :: Size -> RangeSet a -> RangeSet a -> RangeSet a
glue !_ Tip rt = rt
glue _ lt Tip  = lt
glue sz lt@(Fork lh lsz ll lu llt lrt) rt@(Fork rh rsz rl ru rlt rrt)
  | lh < rh = let (# !l, !u, !rt' #) = minDelete rsz rl ru rlt rrt in forkSz sz l u lt rt'
  | otherwise = let (# !l, !u, !lt' #) = maxDelete lsz ll lu llt lrt in forkSz sz l u lt' rt

{-|
Filters a set by removing all values greater than or equal to the given value.

@since 2.1.0.0
-}
{-# INLINEABLE allLess #-}
allLess :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
allLess !_ Tip = Tip
allLess x (Fork _ _ l u lt rt) = case compare x l of
  EQ          -> lt
  LT          -> allLess x lt
  GT | x <= u -> unsafeInsertR (diff l (pred x)) l (pred x) (allLess x lt)
  GT          -> link l u lt (allLess x rt)

{-|
Filters a set by removing all values less than or equal to the given value.

@since 2.1.0.0
-}
{-# INLINEABLE allMore #-}
allMore :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
allMore !_ Tip = Tip
allMore x (Fork _ _ l u lt rt) = case compare u x of
  EQ          -> rt
  LT          -> allMore x rt
  GT | l <= x -> unsafeInsertL (diff (succ x) u) (succ x) u (allMore x rt)
  GT          -> link l u (allMore x lt) rt

{-{-# INLINEABLE unsafeAllLess #-}
unsafeAllLess :: (Enum a, Ord a) => a -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
unsafeAllLess !x !l !u !lt !rt = case compare x l of
  EQ          -> lt
  LT          -> allLess x lt
  GT | x <= u -> unsafeInsertR (diff l (pred x)) l (pred x) (allLess x lt)
  GT          -> link l u lt (allLess x rt)-}

{-{-# INLINEABLE unsafeAllMore #-}
unsafeAllMore :: (Enum a, Ord a) => a -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
unsafeAllMore !x !l !u !lt !rt = case compare u x of
  EQ          -> rt
  LT          -> allMore x rt
  GT | l <= x -> unsafeInsertL (diff (succ x) u) (succ x) u (allMore x rt)
  GT          -> link l u (allMore x lt) rt-}

{-# INLINEABLE split #-}
split :: (Enum a, Ord a) => a -> a -> RangeSet a -> (# RangeSet a, RangeSet a #)
split !_ !_ Tip = (# Tip, Tip #)
split l u (Fork _ _ l' u' lt rt)
  | u < l' = let (# !llt, !lgt #) = split l u lt in (# llt, link l' u' lgt rt #)
  | u' < l = let (# !rlt, !rgt #) = split l u rt in (# link l' u' lt rlt, rgt #)
  -- The ranges overlap in some way
  | otherwise = let !lt' = case compare l' l of
                      EQ -> lt
                      LT -> unsafeInsertR (diff l' (pred l)) l' (pred l) lt
                      GT -> allLess l lt
                    !rt' = case compare u u' of
                      EQ -> rt
                      LT -> unsafeInsertL (diff (succ u) u') (succ u) u' rt
                      GT -> allMore u rt
                in (# lt', rt' #)

{-# INLINE splitOverlap #-}
splitOverlap :: (Enum a, Ord a) => a -> a -> RangeSet a -> (# RangeSet a, RangeSet a, RangeSet a #)
splitOverlap !l !u !t = let (# lt', rt' #) = split l u t in (# lt', overlapping l u t, rt' #)

{-# INLINABLE overlapping #-}
overlapping :: (Ord a, Enum a) => a -> a -> RangeSet a -> RangeSet a
overlapping !_ !_ Tip = Tip
overlapping x y (Fork _ sz l u lt rt) =
  case compare l x of
    -- range is outside to the left
    GT -> let !lt' = overlapping x (min (pred l) y) lt
          in case cmpY of
               -- range is totally outside
               GT -> unsafeLink nodeSz l u lt' rt'
               EQ -> unsafeInsertR nodeSz l u lt'
               LT | y >= l -> unsafeInsertR (diff l y) l y lt'
               LT          -> lt'
    -- range is inside on the left
    EQ -> case cmpY of
      -- range is outside on the right
      GT -> unsafeInsertL nodeSz l u rt'
      LT -> t'
      EQ -> single nodeSz l u
    LT -> case cmpY of
      -- range is outside on the right
      GT | x <= u -> unsafeInsertL (diff x u) x u rt'
      GT          -> rt'
      _           -> t'
  where
    !cmpY = compare y u
    !nodeSz = sz - size lt - size rt
    -- leave lazy!
    rt' = overlapping (max (succ u) x) y rt
    t' = single (diff x y) x y

data StrictMaybe a = SJust !a | SNothing

{-|
Inverts a set: every value which was an element is no longer an element, and every value that
was not an element now is. This is only possible on `Bounded` types.

@since 2.1.0.0
-}
{-# INLINEABLE complement #-}
complement :: forall a. (Bounded a, Enum a, Eq a) => RangeSet a -> RangeSet a
complement Tip = single (diff @a minBound maxBound) minBound maxBound
complement t | full t = Tip
complement t@(Fork _ sz l u lt rt) = t'''
  where
    (# !min, !min' #) = minRange l u lt

    -- The complement of a tree is at most 1 larger or smaller than the original
    -- if both min and max are minBound and maxBound, it will shrink
    -- if neither min or max are minBound or maxBound, it will grow
    -- otherwise, the tree will not change size
    -- The insert or shrink will happen at an extremity, and rebalance need only occur along the spine
    (# !t', !initial #) | min == minBound = (# deleteLeftmost (diff minBound min') sz l u lt rt, succ min' #) -- this is safe, because we've checked for the maxSet case already
                        | otherwise       = (# t , minBound #)
    (# !t'', !final #) = go initial t'
    t''' | SJust x <- final = unsafeInsertR (diff x maxBound) x maxBound t''
         | otherwise        = t''

    safeSucc !x
      | x == maxBound = SNothing
      | otherwise     = SJust (succ x)

    -- the argument l should not be altered, it /must/ be the correct lower bound
    -- the return /must/ be the next correct lower bound
    go :: a -> RangeSet a -> (# RangeSet a, StrictMaybe a #)
    go !l Tip = (# Tip, SJust l #)
    go l (Fork _ _ u l'' lt Tip) =
      let (# !lt', SJust l' #) = go l lt
          !t' = fork l' (pred u) lt' Tip
      in  (# t', safeSucc l'' #)
    go l (Fork _ _ u l'' lt rt) =
      let (# !lt', SJust l' #) = go l lt
          (# !rt', !l''' #) = go (succ l'') rt -- this is safe, because we know the right-tree is not Tip
          !t' = fork l' (pred u) lt' rt'
      in  (# t', l''' #)

{-|
Tests if all the element of the first set appear in the second, but also that the first and second
sets are not equal.

@since 2.1.0.0
-}
{-# INLINE isProperSubsetOf #-}
isProperSubsetOf :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
isProperSubsetOf t1 t2 = size t1 < size t2 && uncheckedSubsetOf t1 t2

{-|
Tests if all the elements of the first set appear in the second.

@since 2.1.0.0
-}
{-# INLINEABLE isSubsetOf #-}
isSubsetOf :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
isSubsetOf t1 t2 = size t1 <= size t2 && uncheckedSubsetOf t1 t2

uncheckedSubsetOf :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
uncheckedSubsetOf Tip _ = True
uncheckedSubsetOf _ Tip = False
uncheckedSubsetOf (Fork _ _ l u lt rt) t = case splitOverlap l u t of
  (# lt', Fork 1 _ x y _ _, rt' #) ->
       x == l && y == u
    && size lt <= size lt' && size rt <= size rt'
    && uncheckedSubsetOf lt lt' && uncheckedSubsetOf rt rt'
  _                              -> False

{-|
Returns all the elements found within the set.

@since 2.1.0.0
-}
{-# INLINE elems #-}
elems :: Enum a => RangeSet a -> [a]
elems t = fold (\l u lt rt -> lt . (range l u ++) . rt) id t []

{-|
Returns all the values that are not found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE unelems #-}
unelems :: (Bounded a, Enum a, Eq a) => RangeSet a -> [a]
unelems t = fold fork tip t minBound maxBound []
  where
    fork l' u' lt rt l u = dxs . dys
      where
        dxs | l' == l   = id
            | otherwise = lt l (pred l')
        dys | u == u'   = id
            | otherwise = rt (succ u') u
    tip l u = (range l u ++)

{-|
Constructs a `RangeSet` given a list of ranges.

@since 2.1.0.0
-}
-- TODO: This could be better?
{-# INLINEABLE fromRanges #-}
fromRanges :: (Enum a, Ord a) => [(a, a)] -> RangeSet a
fromRanges [(x, y)] = single (diff x y) x y
fromRanges rs = foldr (uncurry insertRange) empty rs

{-|
Inserts a range into a `RangeSet`.

@since 2.1.0.0
-}
-- This could be improved, but is OK
{-# INLINE insertRange #-}
insertRange :: (Enum a, Ord a) => a -> a -> RangeSet a -> RangeSet a
insertRange l u t = let (# lt, rt #) = split l u t in link l u lt rt

{-|
Builds a `RangeSet` from a given list of elements.

@since 2.1.0.0
-}
-- TODO: This can be made better if we account for orderedness
{-# INLINE fromList #-}
fromList :: (Enum a, Ord a) => [a] -> RangeSet a
fromList = foldr insert empty

{-|
Folds a range set.

@since 2.1.0.0
-}
{-# INLINEABLE fold #-}
fold :: (a -> a -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
     -> b                       -- ^ Value to be substituted at the leaves.
     -> RangeSet a
     -> b
fold _ tip Tip = tip
fold fork tip (Fork _ _ l u lt rt) = fork l u (fold fork tip lt) (fold fork tip rt)

-- Instances
instance Eq a => Eq (RangeSet a) where
  t1 == t2 = size t1 == size t2 && ranges t1 == ranges t2
    where
      {-# INLINE ranges #-}
      ranges :: RangeSet a -> [(a, a)]
      ranges t = fold (\l u lt rt -> lt . ((l, u) :) . rt) id t []

-- Testing Utilities
valid :: (Ord a, Enum a) => RangeSet a -> Bool
valid t = balanced t && wellSized t && orderedNonOverlappingAndCompressed True t

balanced :: RangeSet a -> Bool
balanced Tip = True
balanced (Fork h _ _ _ lt rt) =
  h == max (height lt) (height rt) + 1 &&
  height rt < h &&
  abs (height lt - height rt) <= 1 &&
  balanced lt &&
  balanced rt

wellSized :: Enum a => RangeSet a -> Bool
wellSized Tip = True
wellSized (Fork _ sz l u lt rt) = sz == size lt + size rt + diff l u && wellSized lt && wellSized rt

orderedNonOverlappingAndCompressed :: (Enum a, Ord a) => Bool -> RangeSet a -> Bool
orderedNonOverlappingAndCompressed checkCompressed = bounded (const True) (const True)
  where
    bounded _ _ Tip = True
    bounded lo hi (Fork _ _ l u lt rt) =
      l <= u &&
      lo l &&
      hi u &&
      bounded lo (boundAbove l) lt &&
      bounded (boundBelow u) hi rt

    boundAbove l | checkCompressed = liftA2 (&&) (< l) (< pred l)
                 | otherwise = (< l)

    boundBelow u | checkCompressed = liftA2 (&&) (> u) (> succ u)
                 | otherwise = (> u)
