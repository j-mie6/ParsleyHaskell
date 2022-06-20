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
    elems, unelems, fromRanges, fromDistinctAscRanges, insertRange, fromList, fromDistinctAscList,
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

{-# INLINE diffE #-}
diffE :: E -> E -> Size
diffE !l !u = u - l + 1

type Size = Int
type E = Int
{-|
A @Set@ type designed for types that are `Enum` as well as `Ord`. This allows the `RangeSet` to
compress the data when it is contiguous, reducing memory-footprint and enabling otherwise impractical
operations like `complement` for `Bounded` types.

@since 2.1.0.0
-}
data RangeSet a = Fork {-# UNPACK #-} !Int {-# UNPACK #-} !Size {-# UNPACK #-} !E {-# UNPACK #-} !E !(RangeSet a) !(RangeSet a)
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
singleton :: Enum a => a -> RangeSet a
singleton x = single 1 (fromEnum x) (fromEnum x)

{-# INLINE heightOfFork #-}
heightOfFork :: Int -> Int -> Int
heightOfFork lh rh = max lh rh + 1

{-# INLINE fork #-}
fork :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = forkSz (size lt + size rt + diffE l u) l u lt rt

--{-# INLINE forkSz #-} -- this does bad things
forkSz :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
forkSz !sz !l !u !lt !rt = forkH sz l u (height lt) lt (height rt) rt

{-# INLINE forkH #-}
forkH :: Size -> E -> E -> Int -> RangeSet a -> Int -> RangeSet a -> RangeSet a
forkH !sz !l !u !lh !lt !rh !rt =  Fork (heightOfFork lh rh) sz l u lt rt

{-# INLINE single #-}
single :: Size -> E -> E -> RangeSet a
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
full :: forall a. (Enum a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ _ l u _ _) = l == fromEnum @a minBound && fromEnum @a maxBound == u

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
extractSingle :: Enum a => RangeSet a -> Maybe a
extractSingle (Fork _ _ x y Tip Tip) | x == y = Just (toEnum x)
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
sizeRanges :: forall a. Enum a => RangeSet a -> Int
sizeRanges = fold @a (\_ _ szl szr -> szl + szr + 1) 0

{-|
Test whether or not a given value is found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE member #-}
member :: forall a. Enum a => a -> RangeSet a -> Bool
member !x = go
  where
    !x' = fromEnum x
    go (Fork _ _ l u lt rt)
      | l <= x'   = x' <= u || go rt
      | otherwise = go lt
    go Tip = False

{-|
Test whether or not a given value is not found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE notMember #-}
notMember :: Enum a => a -> RangeSet a -> Bool
notMember x = not . member x

{-# INLINE ifeq #-}
ifeq :: RangeSet a -> RangeSet a -> RangeSet a -> (RangeSet a -> RangeSet a) -> RangeSet a
ifeq !x !x' y f = if size x == size x' then y else f x'

{-|
Insert a new element into the set.

@since 2.1.0.0
-}
{-# INLINEABLE insert #-}
insert :: Enum a => a -> RangeSet a -> RangeSet a
insert = insertE . fromEnum

{-# INLINEABLE insertE #-}
insertE :: E -> RangeSet a -> RangeSet a
insertE !x Tip = single 1 x x
insertE x t@(Fork h sz l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x = if
    | x <= u -> t
  -- If it is adjacent to the upper range, it may fuse
    | x == succ u -> fuseRight h (sz + 1) l x lt rt                                 -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
    | otherwise -> ifeq rt (insertE x rt) t (balance (sz + 1) l u lt)               -- cannot be biased, because fusion can shrink a tree
  | {- x < l -} otherwise = if
  -- If it is adjacent to the lower, it may fuse
    x == pred l then fuseLeft h (sz + 1) x u lt rt                                  -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
                else ifeq lt (insertE x lt) t $ \lt' -> balance (sz + 1) l u lt' rt -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !h !sz !x !u Tip !rt = Fork h sz x u Tip rt
    fuseLeft h sz x u (Fork _ lsz ll lu llt lrt) rt
      | (# !l, !x', lt' #) <- maxDelete lsz ll lu llt lrt
      -- we know there exists an element larger than x'
      -- if x == x' + 1, we fuse (x != x' since that breaks disjointness, x == pred l)
      , x == succ x' = balanceR sz l u lt' rt
      | otherwise    = Fork h sz x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !h !sz !l !x !lt Tip = Fork h sz l x lt Tip
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
delete :: Enum a => a -> RangeSet a -> RangeSet a
delete = deleteE . fromEnum

{-# INLINEABLE deleteE #-}
deleteE :: E -> RangeSet a -> RangeSet a
deleteE !_ Tip = Tip
deleteE x t@(Fork h sz l u lt rt) =
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
       GT          -> ifeq rt (deleteE x rt) t $ balance (sz - 1) l u lt             -- cannot be biased, because fisson can grow a tree
    GT             -> ifeq lt (deleteE x lt) t $ \lt' -> balance (sz - 1) l u lt' rt -- cannot be biased, because fisson can grow a tree
  where
    {- Fission breaks a node into two new ranges
       we'll push the range down into the smallest child, ensuring it's balanced -}
    {-# INLINE fission #-}
    fission !sz !l1 !x !u2 !lt !rt
      | height lt > height rt = forkSz sz l1 u1 lt (unsafeInsertL sz' l2 u2 rt)
      | otherwise = forkSz sz l1 u1 (unsafeInsertR sz' l2 u2 lt) rt
      where
        !u1 = pred x
        !l2 = succ x
        !sz' = diffE l2 u2

{-|
Inserts an range at the left-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertL #-}
unsafeInsertL :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertL !newSz !l !u = go
  where
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceL (sz + newSz) l' u' (go lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertR !newSz !l !u = go
  where
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceR (sz + newSz) l' u' lt (go rt)

{-|
Find the minimum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMin #-}
findMin :: Enum a => RangeSet a -> Maybe a
findMin Tip = Nothing
findMin (Fork _ _ l u lt _) = let (# !m, !_ #) = minRange l u lt in Just (toEnum m)

{-# INLINEABLE minRange #-}
minRange :: E -> E -> RangeSet a -> (# E, E #)
minRange !l !u Tip                 = (# l, u #)
minRange _  _  (Fork _ _ l u lt _) = minRange l u lt

{-|
Find the maximum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMax #-}
findMax :: Enum a => RangeSet a -> Maybe a
findMax Tip = Nothing
findMax (Fork _ _ l u _ rt) = let (# !_, !m #) = maxRange l u rt in Just (toEnum m)

{-# INLINEABLE maxRange #-}
maxRange :: E -> E -> RangeSet a -> (# E, E #)
maxRange !l !u Tip                 = (# l, u #)
maxRange _  _  (Fork _ _ l u _ rt) = maxRange l u rt

{-# INLINE minDelete #-}
minDelete :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
minDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go !sz !l !u Tip !rt = (# l, u, sz - size rt, rt #)
    go sz l u (Fork _ lsz ll lu llt lrt) rt =
      let (# !ml, !mu, !msz, lt' #) = go lsz ll lu llt lrt
      in (# ml, mu, msz, balanceR (sz - msz) l u lt' rt #)

{-# INLINE maxDelete #-}
maxDelete :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
maxDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go !sz !l !u !lt Tip = (# l, u, sz - size lt, lt #)
    go sz l u lt (Fork _ rsz rl ru rlt rrt) =
      let (# !ml, !mu, !msz, rt' #) = go rsz rl ru rlt rrt
      in (# ml, mu, msz, balanceL (sz - msz) l u lt rt' #)

{-# NOINLINE balance #-}
balance :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
balance !sz !l !u Tip Tip = single sz l u
balance sz l u lt@(Fork lh lsz ll lu llt lrt) Tip
  | lh == 1   = Fork (lh + 1) sz l u lt Tip
  | otherwise = uncheckedBalanceL sz l u lsz ll lu llt lrt Tip
balance sz l u Tip rt@(Fork rh rsz rl ru rlt rrt)
  | rh == 1   = Fork (rh + 1) sz l u Tip rt
  | otherwise = uncheckedBalanceR sz l u Tip rsz rl ru rlt rrt
balance sz l u lt@(Fork lh lsz ll lu llt lrt) rt@(Fork rh rsz rl ru rlt rrt)
  | height lt > height rt + 1 = uncheckedBalanceL sz l u lsz ll lu llt lrt rt
  | height rt > height lt + 1 = uncheckedBalanceR sz l u lt rsz rl ru rlt rrt
  | otherwise = forkH sz l u lh lt rh rt

{-# INLINEABLE balanceL #-}
balanceL :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !sz !l1 !u1 lt@(Fork !lh !lsz !l2 !u2 !llt !lrt) !rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH sz l1 u1 lh lt rh rt
  -- The bias is 2 (dltrt == 2)
  | otherwise  = uncheckedBalanceL sz l1 u1 lsz l2 u2 llt lrt rt
  where
    !rh = height rt
    !dltrt = lh - rh
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL sz l u Tip rt = Fork (height rt + 1) sz l u Tip rt

{-# INLINEABLE balanceR #-}
balanceR :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR !sz !l1 !u1 !lt rt@(Fork !rh !rsz !l2 !u2 !rlt !rrt)
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH sz l1 u1 lh lt rh rt
  | otherwise  = uncheckedBalanceR sz l1 u1 lt rsz l2 u2 rlt rrt
  where
    !lh = height lt
    !dltrt = rh - lh
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR sz l u lt Tip = Fork (height lt + 1) sz l u lt Tip

{-# NOINLINE uncheckedBalanceL #-}
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
uncheckedBalanceL :: Size -> E -> E -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
uncheckedBalanceL !sz !l1 !u1 !szl !l2 !u2 !llt !lrt !rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hlrt = rotr' sz l1 u1 szl l2 u2 llt lrt rt
  | otherwise    = rotr sz l1 u1 (rotl szl l2 u2 llt lrt) rt
  where
    !hllt = height llt
    !hlrt = height lrt

{-# NOINLINE uncheckedBalanceR #-}
uncheckedBalanceR :: Size -> E -> E -> RangeSet a -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
uncheckedBalanceR !sz !l1 !u1 !lt !szr !l2 !u2 !rlt !rrt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hrlt = rotl' sz l1 u1 lt szr l2 u2 rlt rrt
  | otherwise    = rotl sz l1 u1 lt (rotr szr l2 u2 rlt rrt)
  where
    !hrlt = height rlt
    !hrrt = height rrt

{-# INLINE rotr #-}
rotr :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotr !sz !l1 !u1 (Fork _ !szl !l2 !u2 !p !q) !r = rotr' sz l1 u1 szl l2 u2 p q r
rotr _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl !sz !l1 !u1 !p (Fork _ !szr !l2 !u2 !q !r) = rotl' sz l1 u1 p szr l2 u2 q r
rotl _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotr' #-}
rotr' :: Size -> E -> E -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
rotr' !sz !l1 !u1 !szl !l2 !u2 !p !q !r = forkSz sz l2 u2 p (forkSz (sz - szl + size q) l1 u1 q r)

{-# INLINE rotl' #-}
rotl' :: Size -> E -> E -> RangeSet a -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl' !sz !l1 !u1 !p !szr !l2 !u2 !q !r = forkSz sz l2 u2 (forkSz (sz - szr + size q) l1 u1 p q) r

{-|
Unions two sets together such that if and only if an element appears in either one of the sets, it
will appear in the result set.

@since 2.1.0.0
-}
{-# INLINABLE union #-}
union :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
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
intersection :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Fork _ _ l1 u1 lt1 rt1) t2 =
  case overlap of
    Tip -> disjointMerge lt1lt2 rt1rt2
    Fork 1 sz x y _ _
      | x == l1, y == u1
      , lt1lt2 `ptrEq` lt1, rt1rt2 `ptrEq` rt1 -> t1
      | otherwise -> disjointLink sz x y lt1lt2 rt1rt2
    Fork _ sz x y lt' rt' -> disjointLink (sz - size lt' - size rt') x y (disjointMerge lt1lt2 lt') (disjointMerge rt' rt1rt2)
  where
    (# !lt2, !overlap, !rt2 #) = splitOverlap l1 u1 t2
    !lt1lt2 = intersection lt1 lt2
    !rt1rt2 = intersection rt1 rt2

{-|
Do two sets have no elements in common?

@since 2.1.0.0
-}
{-# INLINE disjoint #-}
disjoint :: Enum a => RangeSet a -> RangeSet a -> Bool
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
difference :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
difference Tip _ = Tip
difference t Tip = t
difference t (Fork _ _ l u lt rt) = case split l u t of
  (# lt', rt' #)
    | size lt'lt + size rt'rt == size t -> t
    | otherwise -> disjointMerge lt'lt rt'rt
    where
      !lt'lt = difference lt' lt
      !rt'rt = difference rt' rt

{-# INLINEABLE insertLAdj #-}
insertLAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertLAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case minRange tl tu tlt of
  (# !l', _ #) | l' == succ u -> fuseL newSz l th tsz tl tu tlt trt
               | otherwise    -> balanceL (tsz + newSz) tl tu (unsafeInsertL newSz l u tlt) trt
  where
    {-# INLINEABLE fuseL #-}
    fuseL :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseL !newSz !l' !h !sz !l !u lt rt = case lt of
      Tip -> Fork h (newSz + sz) l' u Tip rt
      Fork lh lsz ll lu llt lrt  -> Fork h (newSz + sz) l u (fuseL newSz l' lh lsz ll lu llt lrt) rt

{-# INLINEABLE insertRAdj #-}
insertRAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertRAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case maxRange tl tu trt of
  (# _, !u' #) | u' == pred l -> fuseR newSz u th tsz tl tu tlt trt
               | otherwise    -> balanceR (tsz + newSz) tl tu tlt (unsafeInsertR newSz l u trt)
  where
    {-# INLINEABLE fuseR #-}
    fuseR :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseR !newSz !u' !h !sz !l !u lt rt = case rt of
      Tip -> Fork h (newSz + sz) l u' lt Tip
      Fork rh rsz rl ru rlt rrt  -> Fork h (newSz + sz) l u lt (fuseR newSz u' rh rsz rl ru rlt rrt)

{-# INLINABLE link #-}
link :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
link !l !u Tip Tip = single (diffE l u) l u
link l u Tip (Fork rh rsz rl ru rlt rrt) = insertLAdj (diffE l u) l u rh rsz rl ru rlt rrt
link l u (Fork lh lsz ll lu llt lrt) Tip = insertRAdj (diffE l u) l u lh lsz ll lu llt lrt
link l u lt@(Fork _ lsz ll lu llt lrt) rt@(Fork _ rsz rl ru rlt rrt) =
  disjointLink (diffE l' u') l' u' lt'' rt''
  where
    -- we have to check for fusion up front
    (# !lmaxl, !lmaxu, lt' #) = maxDelete lsz ll lu llt lrt
    (# !rminl, !rminu, rt' #) = minDelete rsz rl ru rlt rrt

    (# !l', !lt'' #) | lmaxu == pred l = (# lmaxl, lt' #)
                     | otherwise       = (# l, lt #)

    (# !u', !rt'' #) | rminl == succ u = (# rminu, rt' #)
                     | otherwise       = (# u, rt #)

{-# INLINEABLE disjointLink #-}
disjointLink :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
disjointLink !newSz !l !u Tip rt = unsafeInsertL newSz l u rt
disjointLink newSz l u lt Tip = unsafeInsertR newSz l u lt
disjointLink newSz l u lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (newSz + szl + szr) rl ru (disjointLink newSz l u lt rlt) rrt
  | hr < hl + 1 = balanceR (newSz + szl + szr) ll lu llt (disjointLink newSz l u lrt rt)
  | otherwise   = forkH (newSz + szl + szr) l u hl lt hr rt

-- This version checks for fusion between the two trees to be merged
{-{-# INLINEABLE merge #-}
merge :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
merge Tip Tip = Tip
merge t Tip = t
merge Tip t = t
merge t1 t2 =
  let (# !_, !u1 #) = unsafeMaxRange t1
      (# !l2, !u2, t2' #) = unsafeMinDelete t2
  in if succ u1 == l2 then unsafeMerge (unsafeFuseR (diffE l2 u2) u2 t1) t2'
     else unsafeMerge t1 t2-}

-- This assumes that the trees are /totally/ disjoint
{-# INLINEABLE disjointMerge #-}
disjointMerge :: RangeSet a -> RangeSet a -> RangeSet a
disjointMerge Tip rt = rt
disjointMerge lt Tip = lt
disjointMerge lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (szl + szr) rl ru (disjointMerge lt rlt) rrt
  | hr < hl + 1 = balanceR (szl + szr) ll lu llt (disjointMerge lrt rt)
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
allLess :: Enum a => a -> RangeSet a -> RangeSet a
allLess = allLessE . fromEnum

{-# INLINEABLE allLessE #-}
allLessE :: E -> RangeSet a -> RangeSet a
allLessE !_ Tip = Tip
allLessE x (Fork _ _ l u lt rt) = case compare x l of
  EQ          -> lt
  LT          -> allLessE x lt
  GT | x <= u -> unsafeInsertR (diffE l (pred x)) l (pred x) (allLessE x lt)
  GT          -> link l u lt (allLessE x rt)

{-|
Filters a set by removing all values less than or equal to the given value.

@since 2.1.0.0
-}
{-# INLINEABLE allMore #-}
allMore :: Enum a => a -> RangeSet a -> RangeSet a
allMore = allMoreE . fromEnum

{-# INLINEABLE allMoreE #-}
allMoreE :: E -> RangeSet a -> RangeSet a
allMoreE !_ Tip = Tip
allMoreE x (Fork _ _ l u lt rt) = case compare u x of
  EQ          -> rt
  LT          -> allMoreE x rt
  GT | l <= x -> unsafeInsertL (diffE (succ x) u) (succ x) u (allMoreE x rt)
  GT          -> link l u (allMoreE x lt) rt

{-# INLINEABLE split #-}
split :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a #)
split !_ !_ Tip = (# Tip, Tip #)
split l u (Fork _ _ l' u' lt rt)
  | u < l' = let (# !llt, !lgt #) = split l u lt in (# llt, link l' u' lgt rt #)
  | u' < l = let (# !rlt, !rgt #) = split l u rt in (# link l' u' lt rlt, rgt #)
  -- The ranges overlap in some way
  | otherwise = let !lt' = case compare l' l of
                      EQ -> lt
                      LT -> unsafeInsertR (diffE l' (pred l)) l' (pred l) lt
                      GT -> allLessE l lt
                    !rt' = case compare u u' of
                      EQ -> rt
                      LT -> unsafeInsertL (diffE (succ u) u') (succ u) u' rt
                      GT -> allMoreE u rt
                in (# lt', rt' #)

{-# INLINE splitOverlap #-}
splitOverlap :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a, RangeSet a #)
splitOverlap !l !u !t = let (# lt', rt' #) = split l u t in (# lt', overlapping l u t, rt' #)

{-# INLINABLE overlapping #-}
overlapping :: E -> E -> RangeSet a -> RangeSet a
overlapping !_ !_ Tip = Tip
overlapping x y (Fork _ sz l u lt rt) =
  case compare l x of
    -- range is outside to the left
    GT -> let !lt' = {-allMoreEqX-} overlapping x y lt
          in case cmpY of
               -- range is totally outside
               GT -> disjointLink nodeSz l u lt' rt'
               EQ -> unsafeInsertR nodeSz l u lt'
               LT | y >= l -> unsafeInsertR (diffE l y) l y lt'
               LT          -> lt' {-overlapping x y lt-}
    -- range is inside on the left
    EQ -> case cmpY of
      -- range is outside on the right
      GT -> unsafeInsertL nodeSz l u rt'
      LT -> t'
      EQ -> single nodeSz l u
    LT -> case cmpY of
      -- range is outside on the right
      GT | x <= u -> unsafeInsertL (diffE x u) x u rt'
      GT          -> rt' {-overlapping x y rt-}
      _           -> t'
  where
    !cmpY = compare y u
    !nodeSz = sz - size lt - size rt
    -- leave lazy!
    rt' = {-allLessEqY-} overlapping x y rt
    t' = single (diffE x y) x y

    {-allLessEqY Tip = Tip
    allLessEqY (Fork _ sz l u lt rt) = case compare y l of
      EQ         -> unsafeInsertR 1 y y lt
      LT         -> allLessEqY lt
      GT | y < u -> unsafeInsertR (diffE l y) l y (allLessEqY lt)
      GT         -> disjointLink (sz - size lt - size rt) l u lt (allLessEqY rt)

    allMoreEqX Tip = Tip
    allMoreEqX (Fork _ sz l u lt rt) = case compare u x of
      EQ         -> unsafeInsertL 1 x x rt
      LT         -> allMoreEqX rt
      GT | l < x -> unsafeInsertL (diffE x u) x u (allMoreEqX rt)
      GT         -> disjointLink (sz - size lt - size rt) l u (allMoreEqX lt) rt-}

data StrictMaybe a = SJust !a | SNothing

{-|
Inverts a set: every value which was an element is no longer an element, and every value that
was not an element now is. This is only possible on `Bounded` types.

@since 2.1.0.0
-}
{-# INLINEABLE complement #-}
complement :: forall a. (Bounded a, Enum a) => RangeSet a -> RangeSet a
complement Tip = single (diffE minBoundE maxBoundE) minBoundE maxBoundE
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
complement t | full t = Tip
complement t@(Fork _ sz l u lt rt) = case maxl of
  SJust x -> unsafeInsertR (diffE x maxBoundE) x maxBoundE t'
  SNothing -> t'
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
    (# !minl, !minu, !rest #) = minDelete sz l u lt rt

    -- The complement of a tree is at most 1 larger or smaller than the original
    -- if both min and max are minBound and maxBound, it will shrink
    -- if neither min or max are minBound or maxBound, it will grow
    -- otherwise, the tree will not change size
    -- The insert or shrink will happen at an extremity, and rebalance need only occur along the spine
                       -- this is safe, because we've checked for the maxSet case already
    (# !t', !maxl #) | minl == minBoundE = push (succ minu) rest
                     | otherwise         = push minBoundE t

    safeSucc !x
      | x == maxBoundE = SNothing
      | otherwise      = SJust (succ x)

    -- the argument l should not be altered, it /must/ be the correct lower bound
    -- the return /must/ be the next correct lower bound
    push :: E -> RangeSet a -> (# RangeSet a, StrictMaybe E #)
    push !maxl Tip = (# Tip, SJust maxl #)
    push min (Fork _ _ u max lt Tip) =
      let (# !lt', SJust l #) = push min lt
      in  (# fork l (pred u) lt' Tip, safeSucc max #)
    push min (Fork _ _ u l' lt rt@Fork{}) =
      let (# !lt', SJust l #) = push min lt
          -- this is safe, because we know the right-tree contains elements larger than l'
          (# !rt', !max #) = push (succ l') rt
      in  (# fork l (pred u) lt' rt', max #)

{-|
Tests if all the element of the first set appear in the second, but also that the first and second
sets are not equal.

@since 2.1.0.0
-}
{-# INLINE isProperSubsetOf #-}
isProperSubsetOf :: RangeSet a -> RangeSet a -> Bool
isProperSubsetOf t1 t2 = size t1 < size t2 && uncheckedSubsetOf t1 t2

{-|
Tests if all the elements of the first set appear in the second.

@since 2.1.0.0
-}
{-# INLINEABLE isSubsetOf #-}
isSubsetOf :: RangeSet a -> RangeSet a -> Bool
isSubsetOf t1 t2 = size t1 <= size t2 && uncheckedSubsetOf t1 t2

uncheckedSubsetOf :: RangeSet a -> RangeSet a -> Bool
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
unelems :: forall a. (Bounded a, Enum a) => RangeSet a -> [a]
unelems t = foldE fork tip t (fromEnum @a minBound) (fromEnum @a maxBound) []
  where
    fork :: E -> E -> (E -> E -> [a] -> [a]) -> (E -> E -> [a] -> [a]) -> E -> E -> ([a] -> [a])
    fork l' u' lt rt l u = dxs . dys
      where
        dxs | l' == l   = id
            | otherwise = lt l (pred l')
        dys | u == u'   = id
            | otherwise = rt (succ u') u
    tip :: E -> E -> [a] -> [a]
    tip l u = (range (toEnum l) (toEnum u) ++)

{-|
Constructs a `RangeSet` given a list of ranges.

@since 2.1.0.0
-}
fromRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromRanges [] = empty
fromRanges ((x, y):rs) = go rs ey (SRange ex ey :) 1
  where
    !ex = fromEnum x
    !ey = fromEnum y
    go :: [(a, a)] -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !_ k !n = fromDistinctAscRangesSz (k []) n
    go ((x, y):rs) z k n
      -- ordering and disjointness of the ranges broken
      | ex <= z || ey <= z = insertRangeE ex ey (foldr (uncurry insertRange) (fromDistinctAscRangesSz (k []) n) rs)
      | otherwise          = go rs ey (k . (SRange ex ey :)) (n + 1)
      where
        !ex = fromEnum x
        !ey = fromEnum y

{-fromRanges [(x, y)] = single (diffE xe ye) xe ye
  where
    !xe = fromEnum x
    !ye = fromEnum y
fromRanges rs = foldr (uncurry insertRange) empty rs-}

{-|
Constructs a `RangeSet` given a list of ranges that are in ascending order and do not overlap (this is unchecked).

@since 2.2.0.0
-}
fromDistinctAscRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromDistinctAscRanges rs = go rs id 0
  where
    go :: [(a, a)] -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] k !n = fromDistinctAscRangesSz (k []) n
    go ((x, y):rs) k n = go rs (k . (SRange (fromEnum x) (fromEnum y) :)) (n + 1)


data SRange = SRange {-# UNPACK #-} !E {-# UNPACK #-} !E

fromDistinctAscRangesSz :: [SRange] -> Int -> RangeSet a
fromDistinctAscRangesSz rs !n = let (# t, _ #) = go rs 0 (n - 1) in t
  where
    go :: [SRange] -> Int -> Int -> (# RangeSet a, [SRange] #)
    go rs !i !j
      | i > j     = (# Tip, rs #)
      | otherwise =
        let !mid = (i + j) `div` 2
            (# lt, rs' #) = go rs i (mid - 1)
            SRange !l !u : rs'' = rs'
            (# rt, rs''' #) = go rs'' (mid + 1) j
        in (# fork l u lt rt, rs''' #)

{-|
Inserts a range into a `RangeSet`.

@since 2.1.0.0
-}
{-# INLINE insertRange #-}
insertRange :: Enum a => a -> a -> RangeSet a -> RangeSet a
insertRange l u t =
  let !le = fromEnum l
      !ue = fromEnum u
  in insertRangeE le ue t

{-# INLINE insertRangeE #-}
-- This could be improved, but is OK
insertRangeE :: E -> E -> RangeSet a -> RangeSet a
insertRangeE !l !u t = let (# lt, rt #) = split l u t in link l u lt rt

{-|
Builds a `RangeSet` from a given list of elements.

@since 2.1.0.0
-}
fromList :: forall a. Enum a => [a] -> RangeSet a
fromList [] = empty
fromList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k [SRange l u]) n
    go (!x:xs) l u k n
      -- ordering or uniqueness is broken
      | ex <= u      = insertE ex (foldr insert (fromDistinctAscRangesSz (k [SRange l u]) n) xs)
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . (SRange l u :)) (n + 1)
      where !ex = fromEnum x


-- not sure if this one is any use, it avoids one comparison per element...
{-|
Builds a `RangeSet` from a given list of elements that are in ascending order with no duplicates (this is unchecked).

@since 2.1.0.0
-}
fromDistinctAscList :: forall a. Enum a => [a] -> RangeSet a
fromDistinctAscList [] = empty
fromDistinctAscList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k [SRange l u]) n
    go (!x:xs) l u k n
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . (SRange l u :)) (n + 1)
      where !ex = fromEnum x

{-|
Folds a range set.

@since 2.1.0.0
-}
{-# INLINEABLE fold #-}
fold :: Enum a
     => (a -> a -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
     -> b                       -- ^ Value to be substituted at the leaves.
     -> RangeSet a
     -> b
fold fork = foldE (\l u -> fork (toEnum l) (toEnum u))

{-# INLINEABLE foldE #-}
foldE :: (E -> E -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
      -> b                       -- ^ Value to be substituted at the leaves.
      -> RangeSet a
      -> b
foldE _ tip Tip = tip
foldE fork tip (Fork _ _ l u lt rt) = fork l u (foldE fork tip lt) (foldE fork tip rt)

-- Instances
instance Eq (RangeSet a) where
  t1 == t2 = size t1 == size t2 && ranges t1 == ranges t2
    where
      {-# INLINE ranges #-}
      ranges :: RangeSet a -> [(E, E)]
      ranges t = foldE (\l u lt rt -> lt . ((l, u) :) . rt) id t []

-- Testing Utilities
valid :: RangeSet a -> Bool
valid t = balanced t && wellSized t && orderedNonOverlappingAndCompressed True t

balanced :: RangeSet a -> Bool
balanced Tip = True
balanced (Fork h _ _ _ lt rt) =
  h == max (height lt) (height rt) + 1 &&
  height rt < h &&
  abs (height lt - height rt) <= 1 &&
  balanced lt &&
  balanced rt

wellSized :: RangeSet a -> Bool
wellSized Tip = True
wellSized (Fork _ sz l u lt rt) = sz == size lt + size rt + diffE l u && wellSized lt && wellSized rt

orderedNonOverlappingAndCompressed :: Bool -> RangeSet a -> Bool
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
