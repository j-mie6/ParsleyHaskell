{-# LANGUAGE DerivingStrategies, MagicHash #-}
module Parsley.Internal.Common.RangeSet (
    RangeSet(..),
    empty, singleton, null, full, isSingle, extractSingle, size, sizeRanges,
    member, notMember, findMin, findMax,
    insert, delete,
    union, intersection, difference, complement,
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

{-# INLINE rangeSize #-}
rangeSize :: (Enum a, Num a) => a -> a -> Int
rangeSize l u = fromEnum (u - l) + 1

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

data RangeSet a = Fork {-# UNPACK #-} !Int !a !a !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock (Eq, Show)

{-# INLINE empty #-}
empty :: RangeSet a
empty = Tip

singleton :: a -> RangeSet a
singleton x = single x x

fork :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = Fork (max (height lt) (height rt) + 1) l u lt rt

{-# INLINE single #-}
single :: a -> a -> RangeSet a
single !l !u = Fork 1 l u Tip Tip

null :: RangeSet a -> Bool
null Tip = True
null _ = False

full :: (Eq a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ l u _ _) = l == minBound && maxBound == u

isSingle :: Eq a => RangeSet a -> Bool
isSingle = isJust . extractSingle

extractSingle :: Eq a => RangeSet a -> Maybe a
extractSingle (Fork _ x y Tip Tip) | x == y = Just x
extractSingle _                             = Nothing

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _) = h

size :: (Num a, Enum a) => RangeSet a -> Int
size = fold (\(!l) (!u) szl szr -> szl + szr + rangeSize l u) 0

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
    go (Fork _ l u lt rt)
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
insert !x Tip = single x x
insert x t@(Fork _ l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x, x <= u = t
  -- If it is adjacent to the lower, it may fuse
  | x < l, x == pred l = fuseLeft x u lt rt                      -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
  | x < l = ifeq lt (insert x lt) t $ \lt' -> balance l u lt' rt -- cannot be biased, because fusion can shrink a tree#
  -- If it is adjacent to the upper range, it may fuse
  | x == succ u = fuseRight l x lt rt                            -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
  | otherwise = ifeq rt (insert x rt) t (balance l u lt)         -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !x !u Tip !rt = fork x u lt rt
    fuseLeft x u lt rt
      | (l, x') <- unsafeMaxRange lt
      -- we know there exists an element larger than x'
      -- if x == x' or x == x' + 1, we fuse
      -- x >= x' since it is one less than x''s strict upper bound
      -- x >= x' && (x == x' || x == x' + 1) === x >= x' && x <= x' + 1
      , x <= succ x' = balanceR l u (unsafeDeleteRange l x' lt) rt
      | otherwise    = fork x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !l !x !lt Tip = fork l x lt rt
    fuseRight l x lt rt
      | (x', u) <- unsafeMinRange rt
      -- we know there exists an element smaller than x'
      -- if x == x' or x == x' - 1, we fuse
      -- x <= x' since it is one greater than x''s strict lower bound,
      -- x <= x' && (x == x' || x == x' - 1) === x <= x' && x >= x' - 1
      , x >= pred x' = balanceL l u lt (unsafeDeleteRange x' u rt)
      | otherwise    = fork l x lt rt

{-# INLINEABLE delete #-}
delete :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
delete !_ Tip = Tip
delete x t@(Fork h l u lt rt) =
  case compare l x of
    -- If its the only part of the range, the node is removed
    EQ | x == u    -> pullup lt rt
    -- If it's at an extreme, it shrinks the range
       | otherwise -> Fork h (succ l) u lt rt
    LT -> case compare x u of
    -- If it's at an extreme, it shrinks the range
       EQ          -> Fork h l (pred u) lt rt
    -- Otherwise, if it's still in range, the range undergoes fission
       LT          -> fission l x u lt rt
    -- Otherwise delete and balance for one of the left or right
       GT          -> ifeq rt (delete x rt) t (balance l u lt)         -- cannot be biased, because fisson can grow a tree
    GT             -> ifeq lt (delete x lt) t $ \lt' -> balance l u lt' rt -- cannot be biased, because fisson can grow a tree
  where
    pullup Tip rt = rt
    pullup lt Tip = lt
    -- Both lt and rt are known to be non-empty
    -- We'll pull the new parent element arbitrarily from the right
    pullup lt rt  =
      let (l, u) = unsafeMinRange rt
          rt' = unsafeDeleteRange l u rt
      in balanceL l u lt rt'

    {- Fission breaks a node into two new ranges
       we'll push the range down into the right arbitrarily
       To do this, we have to make it a child of the right-tree's left most position. -}
    {-# INLINE fission #-}
    fission !l1 !x !u2 !lt !rt =
      let u1 = pred x
          l2 = succ x
          rt' = unsafeInsertRange l2 u2 rt
      in balanceR l1 u1 lt rt'

{-|
This inserts a range which does not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertRange #-}
unsafeInsertRange :: Ord a => a -> a -> RangeSet a -> RangeSet a
unsafeInsertRange l u Tip = single l u
unsafeInsertRange l u (Fork _ l' u' lt rt)
  | u < l' = balanceL l' u' (unsafeInsertRange l u lt) rt
  | otherwise = balanceR l' u' lt (unsafeInsertRange l u rt)

{-|
This deletes a range which occurs /exactly/ as specific at the extremities of the tree.
It *must not* be used with an empty tree, and it *must not* be used with a range that may
overlap several elements or be contained within another range. The range to be removed *must* occur
at a semi-leaf node (with at least one Tip).
-}
{-# INLINEABLE unsafeDeleteRange #-}
unsafeDeleteRange :: Ord a => a -> a -> RangeSet a -> RangeSet a
unsafeDeleteRange !l !u (Fork _ l' u' lt Tip) | l == l', u == u' = lt
unsafeDeleteRange l u (Fork _ l' u' Tip rt) | l == l', u == u' = rt
unsafeDeleteRange l u t@(Fork _ l' u' lt rt)
 | l < l' = balanceR l' u' (unsafeDeleteRange l u lt) rt
 | u > u' = balanceL l' u' lt (unsafeDeleteRange l u rt)
 | otherwise = t
unsafeDeleteRange _ _ Tip = error "unsafeDeleteRange called on empty tree"

{-# INLINE findMin #-}
findMin :: Ord a => RangeSet a -> Maybe a
findMin Tip = Nothing
findMin t = Just (fst (unsafeMinRange t))

-- | Should /not/ be called with an empty tree!
{-# INLINEABLE unsafeMinRange #-}
unsafeMinRange :: Ord a => RangeSet a -> (a, a)
unsafeMinRange (Fork _ l u Tip _) = (l, u)
unsafeMinRange (Fork _ _ _ lt _) = unsafeMinRange lt
unsafeMinRange Tip = error "unsafeMinRange called on empty tree"

{-# INLINE findMax #-}
findMax :: Ord a => RangeSet a -> Maybe a
findMax Tip = Nothing
findMax t = Just (snd (unsafeMaxRange t))

-- | Should /not/ be called with an empty tree!
{-# INLINEABLE unsafeMaxRange #-}
unsafeMaxRange :: Ord a => RangeSet a -> (a, a)
unsafeMaxRange (Fork _ l u _ Tip) = (l, u)
unsafeMaxRange (Fork _ _ _ _ rt) = unsafeMaxRange rt
unsafeMaxRange Tip = error "unsafeMaxRange called on empty tree"

{-# INLINABLE balance #-}
balance :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
balance !l !u lt rt
  | height lt > height rt + 1 = balanceL l u lt rt
  | height rt > height lt + 1 = balanceR l u lt rt
  | otherwise = fork l u lt rt

{-# NOINLINE balanceL #-}
balanceL :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !l1 !u1 lt@(Fork !hlt l2 u2 llt rlt) !rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = fork l1 u1 lt rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hrlt = rotr l1 u1 lt rt
  | otherwise    = rotr l1 u1 (rotl l2 u2 llt rlt) rt
  where
    !dltrt = hlt - height rt
    !hllt = height llt
    !hrlt = height rlt
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL l u Tip rt | height rt <= 1 = fork l u rt Tip
balanceL _ _ Tip _ = error "Right should have shrank, but is still 1 taller than a Tip!"

{-# NOINLINE balanceR #-}
balanceR :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR !l1 !u1 !lt rt@(Fork !hrt l2 u2 lrt rrt)
  -- both sides are equal height or off by one
  | drtlt <= 1 = fork l1 u1 lt rt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hlrt = rotl l1 u1 lt rt
  | otherwise    = rotl l1 u1 lt (rotr l2 u2 lrt rrt)
  where
    !drtlt = hrt - height lt
    !hlrt = height lrt
    !hrrt = height rrt
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR l u lt Tip | height lt <= 1 = fork l u lt Tip
balanceR _ _ _ Tip = error "Left should have shrank, but is still 1 taller than a Tip!"

{-# INLINE rotr #-}
rotr :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotr !l1 !u1 (Fork _ l2 u2 p q) !r = fork l2 u2 p (fork l1 u1 q r)
rotr _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotl !l1 !u1 !p (Fork _ l2 u2 q r) = fork l2 u2 (fork l1 u1 p q) r
rotl _ _ _ _ = error "rotr on Tip"

-- TODO: This can be /much much/ better
union :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
union t = foldr insert t . elems

-- TODO: This can be /much much/ better
intersection :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
intersection t = fromList . filter (flip member t) . elems -- difference t . complement <- good if difference is optimised

-- TODO: This can be /much much/ better
difference :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
difference t = foldr delete t . elems

-- TODO: This can be /much much/ better
complement :: (Bounded a, Enum a, Ord a) => RangeSet a -> RangeSet a
complement = fromList . unelems

elems :: Enum a => RangeSet a -> [a]
elems t = fold (\l u lt rt -> lt . (range l u ++) . rt) id t []

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
fromRanges [(x, y)] = single x y
fromRanges rs = fromList (concatMap (uncurry range) rs)

insertRange :: (Enum a, Ord a) => (a, a) -> RangeSet a -> RangeSet a
insertRange = union . fromRanges . pure

fromList :: (Enum a, Ord a) => [a] -> RangeSet a
fromList = foldr insert empty

fold :: (a -> a -> b -> b -> b) -> b -> RangeSet a -> b
fold _ tip Tip = tip
fold fork tip (Fork _ l u lt rt) = fork l u (fold fork tip lt) (fold fork tip rt)

-- Testing Utilities
valid :: (Ord a, Enum a) => RangeSet a -> Bool
valid t = balanced t && orderedNonOverlappingAndCompressed True t

balanced :: RangeSet a -> Bool
balanced Tip = True
balanced (Fork h _ _ lt rt) =
  h == max (height lt) (height rt) + 1 &&
  height rt < h &&
  abs (height lt - height rt) <= 1 &&
  balanced lt &&
  balanced rt

orderedNonOverlappingAndCompressed :: (Enum a, Ord a) => Bool -> RangeSet a -> Bool
orderedNonOverlappingAndCompressed checkCompressed = bounded (const True) (const True)
  where
    bounded _ _ Tip = True
    bounded lo hi (Fork _ l u lt rt) =
      l <= u &&
      lo l &&
      hi u &&
      bounded lo (boundAbove l) lt &&
      bounded (boundBelow u) hi rt

    boundAbove l | checkCompressed = liftA2 (&&) (< l) (< pred l)
                 | otherwise = (< l)

    boundBelow u | checkCompressed = liftA2 (&&) (> u) (> succ u)
                 | otherwise = (> u)