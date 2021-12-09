module Parsley.Internal.Common.RangeSet (
    RangeSet,
    empty, null, size,
    member, notMember,
    insert,
    union, intersection, difference,
    elems, fromRanges, fromList
  ) where

import Prelude hiding (null)
import Data.Ix (Ix)

import qualified Data.Ix as Ix

{-# INLINE rangeSize #-}
rangeSize :: Ix a => a -> a -> Int
rangeSize l u = Ix.rangeSize (l, u)

{-# INLINE inRange #-}
inRange :: Ix a => a -> a -> a -> Bool
inRange l u = Ix.inRange (l, u)

{-# INLINE range #-}
range :: Ix a => a -> a -> [a]
range l u = Ix.range (l, u)

data RangeSet a = Fork {-# UNPACK #-} !Int !a !a !(RangeSet a) !(RangeSet a)
                | Tip

empty :: RangeSet a
empty = Tip

fork :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = Fork (max (height lt) (height rt) + 1) l u lt rt

null :: RangeSet a -> Bool
null Tip = True
null _ = False

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _) = h

size :: Ix a => RangeSet a -> Int
size = foldRangeSet (\(!l) (!u) szl szr -> szl + szr + rangeSize l u) 0

member :: Ix a => a -> RangeSet a -> Bool
member x = foldRangeSet (\(!l) (!u) lt rt -> inRange l u x || (x > u && rt) || lt) False
{-member !x (Fork _ l u lt rt)
  | inRange l u x       = True
  | x > u               = member x rt
  | otherwise {-x < l-} = member x lt
member _ Tip = False-}

notMember :: Ix a => a -> RangeSet a -> Bool
notMember x = not . member x

insert :: (Enum a, Ix a) => a -> RangeSet a -> RangeSet a
insert x Tip = fork x x Tip Tip
insert x t@(Fork _ l u lt rt)
  -- Nothing happens when it's already in range
  | inRange l u x = t
  -- If it is adjacent to the lower or upper range, it may fuse with adjacent ranges
  --  | x == pred l = undefined
  --  | x == succ u = undefined
  -- Otherwise, insert and balance for one of the left or the right
  | x < l = balanceL l u (insert x lt) rt
  | otherwise = balanceR l u lt (insert x rt)

{-# NOINLINE balanceL #-}
balanceL :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL l1 u1 lt@(Fork !hlt l2 u2 llt rlt) rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = fork l1 u1 lt rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hrlt = rotr l1 u1 lt rt
  | otherwise    = rotr l1 u1 (rotl l2 u2 llt rlt) rt
  where
    !dltrt = hlt - height rt
    !hllt = height llt
    !hrlt = height rlt
balanceL _ _ _ _ = error "Left tree didn't grow (or right didn't shrink), but balanceL was called!"

{-# NOINLINE balanceR #-}
balanceR :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR l1 u1 lt rt@(Fork !hrt l2 u2 lrt rrt)
  -- both sides are equal height or off by one
  | drtlt <= 1 = fork l1 u1 lt rt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hlrt = rotl l1 u1 lt rt
  | otherwise    = rotl l1 u1 lt (rotr l2 u2 lrt rrt)
  where
    !drtlt = hrt - height lt
    !hlrt = height lrt
    !hrrt = height rrt
balanceR _ _ _ _ = error "Right tree didn't grow (or left didn't shrink), but balanceR was called!"

{-# INLINE rotr #-}
rotr :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotr l1 u1 (Fork _ l2 u2 p q) r = fork l2 u2 p (fork l1 u1 q r)
rotr _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotl l1 u1 p (Fork _ l2 u2 q r) = fork l2 u2 (fork l1 u1 p q) r
rotl _ _ _ _ = error "rotr on Tip"

-- TODO: This can be /much much/ better
union :: (Enum a, Ix a) => RangeSet a -> RangeSet a -> RangeSet a
union t = foldr insert t . elems

-- TODO: This can be /much much/ better
intersection :: (Enum a, Ix a) => RangeSet a -> RangeSet a -> RangeSet a
intersection t = fromList . filter (flip member t) . elems

-- TODO: This can be /much much/ better
difference :: (Enum a, Ix a) => RangeSet a -> RangeSet a -> RangeSet a
difference t1 t2 = fromList (filter (not . flip member t2) (elems t1))

elems :: Ix a => RangeSet a -> [a]
elems t = foldRangeSet (\l u lt rt -> lt . (range l u ++) . rt) id t []

-- TODO: This can be /much much/ better
fromRanges :: (Enum a, Ix a) => [(a, a)] -> RangeSet a
fromRanges = fromList . concatMap Ix.range

fromList :: (Enum a, Ix a) => [a] -> RangeSet a
fromList = foldr insert empty

foldRangeSet :: (a -> a -> b -> b -> b) -> b -> RangeSet a -> b
foldRangeSet _ tip Tip = tip
foldRangeSet fork tip (Fork _ l u lt rt) = fork l u (foldRangeSet fork tip lt) (foldRangeSet fork tip rt)