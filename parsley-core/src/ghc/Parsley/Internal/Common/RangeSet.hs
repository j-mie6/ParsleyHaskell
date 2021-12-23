{-# LANGUAGE DerivingStrategies, MagicHash, UnboxedTuples, RoleAnnotations, TypeApplications #-}
module Parsley.Internal.Common.RangeSet (
    RangeSet(..),
    empty, singleton, null, full, isSingle, extractSingle, size, sizeRanges,
    member, notMember, findMin, findMax,
    insert, delete,
    union, intersection, difference, disjoint, complement,
    isSubsetOf, isProperSubsetOf,
    elems, unelems, fromRanges, insertRange, fromList,
    fold,
    -- Testing
    valid
  ) where

import Prelude hiding (null)
import Control.Applicative (liftA2)

import Data.Maybe (isJust)

import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

{-# INLINE diff #-}
diff :: Enum a => a -> a -> Int
diff !l !u = fromEnum u - fromEnum l + 1

data RangeSet a = Fork {-# UNPACK #-} !Int {-# UNPACK #-} !Int !a !a !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock Show
type role RangeSet nominal

{-# INLINE empty #-}
empty :: RangeSet a
empty = Tip

singleton :: a -> RangeSet a
singleton x = single 1 x x

fork :: Enum a => a -> a -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = forkSz (size lt + size rt + diff l u) l u lt rt

forkSz :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
forkSz !sz !l !u !lt !rt = Fork (max (height lt) (height rt) + 1) sz l u lt rt

{-# INLINE single #-}
single :: Int -> a -> a -> RangeSet a
single !sz !l !u = Fork 1 sz l u Tip Tip

null :: RangeSet a -> Bool
null Tip = True
null _ = False

full :: (Eq a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ _ l u _ _) = l == minBound && maxBound == u

isSingle :: Eq a => RangeSet a -> Bool
isSingle = isJust . extractSingle

extractSingle :: Eq a => RangeSet a -> Maybe a
extractSingle (Fork _ _ x y Tip Tip) | x == y = Just x
extractSingle _                               = Nothing

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _ _) = h

{-# INLINE size #-}
size :: RangeSet a -> Int
size Tip = 0
size (Fork _ sz _ _ _ _) = sz

sizeRanges :: RangeSet a -> Int
sizeRanges = fold (\_ _ szl szr -> szl + szr + 1) 0

{-# INLINEABLE member #-}
-- One of these is better than the other, I'm just not entirely sure which...
member :: forall a. Ord a => a -> RangeSet a -> Bool
{-
RangeSet/member/Pathological             mean 83.88 μs  ( +- 2.851 μs  )
RangeSet/member/4 way split              mean 11.94 μs  ( +- 4.297 μs  )
RangeSet/member/Small                    mean 177.7 ns  ( +- 4.033 ns  )
RangeSet/member/alphaNum                 mean 1.776 μs  ( +- 17.81 ns  )
-}{-
member !x (Fork _ l u lt rt)
  | l <= x    = x <= u || member x rt
  | otherwise = member x lt
member _ Tip = False-}
{-
RangeSet/member/Pathological             mean 91.04 μs  ( +- 21.57 μs  )
RangeSet/member/4 way split              mean 11.03 μs  ( +- 380.2 ns  )
RangeSet/member/Small                    mean 161.2 ns  ( +- 2.453 ns  )
RangeSet/member/alphaNum                 mean 1.672 μs  ( +- 18.76 ns  )
-}--{-
member !x = go
  where
    go (Fork _ _ l u lt rt)
      | l <= x    = x <= u || go rt
      | otherwise = go lt
    go Tip = False
{-
RangeSet/member/Pathological             mean 83.29 μs  ( +- 2.166 μs  )
RangeSet/member/4 way split              mean 16.11 μs  ( +- 2.771 μs  )
RangeSet/member/Small                    mean 268.9 ns  ( +- 23.04 ns  )
RangeSet/member/alphaNum                 mean 1.689 μs  ( +- 40.04 ns  )
-}{-
member !x = goR
  where
    goR :: RangeSet a -> Bool
    -- check the top most level
    goR Tip = False
    -- we can pick the correct left-hand tree to explore here, passing down the lower bound
    goR (Fork _ l u lt rt)
      | x <= u    = goL l lt
      | otherwise = goR rt

    goL :: a -> RangeSet a -> Bool
    -- if we reach a tip, we check the tightest lower bound above us against x
    goL !l Tip = l <= x
    goL l (Fork _ l' u' lt rt)
      -- otherwise, if x is less than our upper bound, search in the left, refine the lower bound
      | x <= u'   = goL l' lt
      -- x is above our range, but known to be less than our parents upper bound
      -- we should therefore search to our right, preserving the parents lower bound
      | otherwise = goL l rt-}

{-# INLINEABLE notMember #-}
notMember :: Ord a => a -> RangeSet a -> Bool
notMember x = not . member x

{-# INLINE ifeq #-}
ifeq :: a -> a -> a -> (a -> a) -> a
ifeq !x !x' y f = if ptrEq x x' then y else f x'

{-# INLINEABLE insert #-}
insert :: forall a. (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
insert !x Tip = single 1 x x
insert x t@(Fork h sz l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x, x <= u = t
  -- If it is adjacent to the lower, it may fuse
  | x < l, x == pred l = fuseLeft h (sz + 1) x u lt rt                    -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
  | x < l = ifeq lt (insert x lt) t $ \lt' -> balance (sz + 1) l u lt' rt -- cannot be biased, because fusion can shrink a tree#
  -- If it is adjacent to the upper range, it may fuse
  | x == succ u = fuseRight h (sz + 1) l x lt rt                          -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
  | otherwise = ifeq rt (insert x rt) t (balance (sz + 1) l u lt)         -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !h !sz !x !u Tip !rt = Fork h sz x u lt rt
    fuseLeft h sz x u lt rt
      | (# !l, !x' #) <- unsafeMaxRange lt
      -- we know there exists an element larger than x'
      -- if x == x' or x == x' + 1, we fuse
      -- x >= x' since it is one less than x''s strict upper bound
      -- x >= x' && (x == x' || x == x' + 1) === x >= x' && x <= x' + 1
      , x <= succ x' = balanceR sz l u (unsafeDeleteR (diff l x') lt) rt
      | otherwise    = Fork h sz x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !h !sz !l !x !lt Tip = Fork h sz l x lt rt
    fuseRight h sz l x lt rt
      | (# !x', !u #) <- unsafeMinRange rt
      -- we know there exists an element smaller than x'
      -- if x == x' or x == x' - 1, we fuse
      -- x <= x' since it is one greater than x''s strict lower bound,
      -- x <= x' && (x == x' || x == x' - 1) === x <= x' && x >= x' - 1
      , x >= pred x' = balanceL sz l u lt (unsafeDeleteL (diff x' u) rt)
      | otherwise    = Fork h sz l x lt rt

{-# INLINEABLE delete #-}
delete :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
delete !_ Tip = Tip
delete x t@(Fork h sz l u lt rt) =
  case compare l x of
    -- If its the only part of the range, the node is removed
    EQ | x == u    -> pullup (sz - 1) lt rt
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
    pullup !_ Tip rt = rt
    pullup _ lt Tip = lt
    -- Both lt and rt are known to be non-empty
    -- We'll pull the new parent element arbitrarily from the right
    pullup sz lt rt  =
      let (# !l, !u #) = unsafeMinRange rt
          rt' = unsafeDeleteL (diff l u) rt
      in balanceL sz l u lt rt'

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
unsafeInsertL :: Int -> a -> a -> RangeSet a -> RangeSet a
unsafeInsertL !newSz l u Tip = single newSz l u
unsafeInsertL newSz l u (Fork _ sz l' u' lt rt) = balanceL (sz + newSz) l' u' (unsafeInsertL newSz l u lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: Int -> a -> a -> RangeSet a -> RangeSet a
unsafeInsertR !newSz l u Tip = single newSz l u
unsafeInsertR newSz l u (Fork _ sz l' u' lt rt) = balanceR (sz + newSz) l' u' lt (unsafeInsertR newSz l u rt)

{-|
This deletes the left-most range of the tree.
It *must not* be used with an empty tree.
-}
{-# INLINEABLE unsafeDeleteL #-}
unsafeDeleteL ::Int -> RangeSet a -> RangeSet a
unsafeDeleteL !_ (Fork _ _ _ _ Tip rt) = rt
unsafeDeleteL szRemoved (Fork _ sz l u lt rt) = balanceR (sz - szRemoved) l u (unsafeDeleteL szRemoved lt) rt
unsafeDeleteL _ _ = error "unsafeDeleteL called on empty tree"

{-|
This deletes the right-most range of the tree.
It *must not* be used with an empty tree.
-}
{-# INLINEABLE unsafeDeleteR #-}
unsafeDeleteR :: Int -> RangeSet a -> RangeSet a
unsafeDeleteR !_ (Fork _ _ _ _ lt Tip) = lt
unsafeDeleteR szRemoved (Fork _ sz l u lt rt) = balanceL (sz - szRemoved) l u lt (unsafeDeleteR szRemoved rt)
unsafeDeleteR _ _ = error "unsafeDeleteR called on empty tree"

{-# INLINE findMin #-}
findMin :: RangeSet a -> Maybe a
findMin Tip = Nothing
findMin t = let (# !m, !_ #) = unsafeMinRange t in Just m

-- | Should /not/ be called with an empty tree!
{-# INLINEABLE unsafeMinRange #-}
unsafeMinRange :: RangeSet a -> (# a, a #)
unsafeMinRange (Fork _ _ l u Tip _) = (# l, u #)
unsafeMinRange (Fork _ _ _ _ lt _) = unsafeMinRange lt
unsafeMinRange Tip = error "unsafeMinRange called on empty tree"

{-# INLINE findMax #-}
findMax :: RangeSet a -> Maybe a
findMax Tip = Nothing
findMax t = let (# !_, !m #) = unsafeMaxRange t in Just m

-- | Should /not/ be called with an empty tree!
{-# INLINEABLE unsafeMaxRange #-}
unsafeMaxRange :: RangeSet a -> (# a, a #)
unsafeMaxRange (Fork _ _ l u _ Tip) = (# l, u #)
unsafeMaxRange (Fork _ _ _ _ _ rt) = unsafeMaxRange rt
unsafeMaxRange Tip = error "unsafeMaxRange called on empty tree"

{-# INLINABLE balance #-}
balance :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
balance !sz !l !u lt rt
  | height lt > height rt + 1 = balanceL sz l u lt rt
  | height rt > height lt + 1 = balanceR sz l u lt rt
  | otherwise = forkSz sz l u lt rt

{-# NOINLINE balanceL #-}
balanceL :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !sz !l1 !u1 lt@(Fork !hlt szl l2 u2 llt rlt) !rt
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
balanceR :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
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
rotr :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotr !sz !l1 !u1 (Fork _ szl l2 u2 p q) !r = forkSz sz l2 u2 p (forkSz (sz - szl + size q) l1 u1 q r)
rotr _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: Int -> a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotl !sz !l1 !u1 !p (Fork _ szr l2 u2 q r) = forkSz sz l2 u2 (forkSz (sz - szr + size q) l1 u1 p q) r
rotl _ _ _ _ _ = error "rotr on Tip"

-- TODO: This can be /much much/ better
union :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
union t = foldr insert t . elems

-- TODO: This can be /much much/ better
intersection :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
intersection t = fromList . filter (`member` t) . elems
                 -- difference t . complement <- good if difference is optimised

-- TODO: This can be done better
disjoint :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
disjoint t1 t2 = null (intersection t1 t2)

-- TODO: This can be /much much/ better
difference :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
difference t = foldr delete t . elems

data StrictMaybe a = SJust !a | SNothing

{-# INLINEABLE complement #-}
complement :: forall a. (Bounded a, Enum a, Eq a) => RangeSet a -> RangeSet a
complement Tip = single (fromEnum @a maxBound + 1) minBound maxBound
complement t | full t = Tip
complement t@Fork{} = t'''
  where
    (# !min, !min' #) = unsafeMinRange t

    -- The complement of a tree is at most 1 larger or smaller than the original
    -- if both min and max are minBound and maxBound, it will shrink
    -- if neither min or max are minBound or maxBound, it will grow
    -- otherwise, the tree will not change size
    -- The insert or shrink will happen at an extremity, and rebalance need only occur along the spine
    (# !t', !initial #) | min == minBound = (# unsafeDeleteL (fromEnum min' + 1) t, succ min' #) -- this is safe, because we've checked for the maxSet case already
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

isProperSubsetOf :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
isProperSubsetOf t1 t2 = size t1 < size t2 && isSubsetOf t1 t2

-- TODO: This can be done better
isSubsetOf :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> Bool
isSubsetOf t1 t2 =
  --intersection t1 t2 == t1
  --union t1 t2 == t2
  null (difference t1 t2)

elems :: Enum a => RangeSet a -> [a]
elems t = fold (\l u lt rt -> lt . (range l u ++) . rt) id t []

ranges :: RangeSet a -> [(a, a)]
ranges t = fold (\l u lt rt -> lt . ((l, u) :) . rt) id t []

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

-- TODO: This can be /much much/ better
fromRanges :: (Enum a, Ord a) => [(a, a)] -> RangeSet a
fromRanges [(x, y)] = single (diff x y) x y
fromRanges rs = fromList (concatMap (uncurry range) rs)

insertRange :: (Enum a, Ord a) => (a, a) -> RangeSet a -> RangeSet a
insertRange = union . fromRanges . pure

fromList :: (Enum a, Ord a) => [a] -> RangeSet a
fromList = foldr insert empty

fold :: (a -> a -> b -> b -> b) -> b -> RangeSet a -> b
fold _ tip Tip = tip
fold fork tip (Fork _ _ l u lt rt) = fork l u (fold fork tip lt) (fold fork tip rt)

-- Instances
instance Eq a => Eq (RangeSet a) where
  t1 == t2 = size t1 == size t2 && ranges t1 == ranges t2

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