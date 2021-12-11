{-# LANGUAGE DerivingStrategies #-}
module Parsley.Internal.Common.RangeSet (
    RangeSet(..),
    empty, null, size, sizeRanges,
    member, notMember, findMin, findMax,
    insert, delete,
    union, intersection, difference,
    elems, fromRanges, insertRange, fromList,
    -- Testing
    valid
  ) where

import Prelude hiding (null)
import Control.Applicative (liftA2)

{-# INLINE rangeSize #-}
rangeSize :: (Enum a, Num a) => a -> a -> Int
rangeSize l u = fromEnum (u - l) + 1

{-# INLINE inRange #-}
inRange :: Ord a => a -> a -> a -> Bool
inRange l u x = l <= x && x <= u

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

data RangeSet a = Fork {-# UNPACK #-} !Int !a !a !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock (Eq, Show)

empty :: RangeSet a
empty = Tip

fork :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = Fork (max (height lt) (height rt) + 1) l u lt rt

single :: a -> a -> RangeSet a
single !l !u = Fork 1 l u Tip Tip

null :: RangeSet a -> Bool
null Tip = True
null _ = False

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _) = h

size :: (Num a, Enum a) => RangeSet a -> Int
size = foldRangeSet (\(!l) (!u) szl szr -> szl + szr + rangeSize l u) 0

sizeRanges :: RangeSet a -> Int
sizeRanges = foldRangeSet (\_ _ szl szr -> szl + szr + 1) 0

member :: Ord a => a -> RangeSet a -> Bool
member x = foldRangeSet (\(!l) (!u) lt rt -> inRange l u x || (x > u && rt) || lt) False
{-member !x (Fork _ l u lt rt)
  | inRange l u x       = True
  | x > u               = member x rt
  | otherwise {-x < l-} = member x lt
member _ Tip = False-}

notMember :: Ord a => a -> RangeSet a -> Bool
notMember x = not . member x

insert :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
insert x Tip = single x x
insert x t@(Fork _ l u lt rt)
  -- Nothing happens when it's already in range
  | inRange l u x = t
  -- If it is adjacent to the lower or upper range, it may fuse with adjacent ranges
  | x < l, x == pred l = fuseLeft x u lt rt
  | x > u, x == succ u = fuseRight l x lt rt
  -- Otherwise, insert and balance for one of the left or the right
  | x < l = balance l u (insert x lt) rt     -- cannot be biased, because fusion can shrink a tree
  | otherwise = balance l u lt (insert x rt) -- cannot be biased, because fusion can shrink a tree
  where
    fuseLeft x u lt rt
      | not (null lt)
      , (l, x') <- unsafeMaxRange lt
      -- we know there exists an element larger than x'
      -- if x == x' or x == x' + 1, we fuse
      -- x >= x' since it is one less than x''s strict upper bound
      -- x >= x' && (x == x' || x == x' + 1) === x >= x' && x <= x' + 1
      , x <= succ x' = balanceR l u (unsafeDeleteRange l x' lt) rt
      | otherwise    = fork x u lt rt
    fuseRight l x lt rt
      | not (null rt)
      , (x', u) <- unsafeMinRange rt
      -- we know there exists an element smaller than x'
      -- if x == x' or x == x' - 1, we fuse
      -- x <= x' since it is one greater than x''s strict lower bound,
      -- x <= x' && (x == x' || x == x' - 1) === x <= x' && x >= x' - 1
      , x >= pred x' = balanceL l u lt (unsafeDeleteRange x' u rt)
      | otherwise    = fork l x lt rt

delete :: (Enum a, Ord a) => a -> RangeSet a -> RangeSet a
delete _ Tip = Tip
delete x (Fork h l u lt rt)
  -- If its the only part of the range, the node is removed
  | l == x, x == u = pullup lt rt
  -- If it's at an extreme, it shrinks the range
  | l == x = Fork h (succ l) u lt rt
  | x == u = Fork h l (pred u) lt rt
  -- Otherwise, if it's still in range, the range undergoes fission
  | inRange l u x = fission l x u lt rt
  -- Otherwise delete and balance for one of the left or right
  | x < l = balance l u (delete x lt) rt     -- cannot be biased, because fisson can grow a tree
  | otherwise = balance l u lt (delete x rt) -- cannot be biased, because fisson can grow a tree
  where
    pullup Tip rt = rt
    pullup lt Tip = lt
    -- Both lt and rt are known to be non-empty
    -- We'll pull the new parent element arbitrarily from the right
    pullup lt rt  =
      let (l, u) = unsafeMinRange rt
          rt' = unsafeDeleteRange l u rt
      in balanceL l u lt rt'

    {-| Fission breaks a node into two new ranges
        we'll push the range down into the right arbitrarily
        To do this, we have to make it a child of the right-tree's left most position. -}
    fission l1 x u2 lt rt =
      let u1 = pred x
          l2 = succ x
          rt' = unsafeInsertRange l2 u2 rt
      in balanceR l1 u1 lt rt'

{-|
This inserts a range which does not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
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
unsafeDeleteRange :: Ord a => a -> a -> RangeSet a -> RangeSet a
unsafeDeleteRange l u (Fork _ l' u' lt Tip) | l == l', u == u' = lt
unsafeDeleteRange l u (Fork _ l' u' Tip rt) | l == l', u == u' = rt
unsafeDeleteRange l u t@(Fork _ l' u' lt rt)
 | l < l' = balanceR l' u' (unsafeDeleteRange l u lt) rt
 | u > u' = balanceL l' u' lt (unsafeDeleteRange l u rt)
 | otherwise = t
unsafeDeleteRange _ _ Tip = error "unsafeDeleteRange called on empty tree"

findMin :: Ord a => RangeSet a -> Maybe a
findMin Tip = Nothing
findMin t = Just (fst (unsafeMinRange t))

-- | Should /not/ be called with an empty tree!
unsafeMinRange :: Ord a => RangeSet a -> (a, a)
unsafeMinRange (Fork _ l u Tip _) = (l, u)
unsafeMinRange (Fork _ _ _ lt _) = unsafeMinRange lt
unsafeMinRange Tip = error "unsafeMinRange called on empty tree"

findMax :: Ord a => RangeSet a -> Maybe a
findMax Tip = Nothing
findMax t = Just (snd (unsafeMaxRange t))

-- | Should /not/ be called with an empty tree!
unsafeMaxRange :: Ord a => RangeSet a -> (a, a)
unsafeMaxRange (Fork _ l u _ Tip) = (l, u)
unsafeMaxRange (Fork _ _ _ _ rt) = unsafeMaxRange rt
unsafeMaxRange Tip = error "unsafeMaxRange called on empty tree"

{-# NOINLINE balance #-}
balance :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
balance l u lt rt
  | height lt > height rt + 1 = balanceL l u lt rt
  | height rt > height lt + 1 = balanceR l u lt rt
  | otherwise = fork l u lt rt

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
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL l u Tip rt | height rt <= 1 = fork l u rt Tip
balanceL _ _ Tip _ = error "Right should have shrank, but is still 1 taller than a Tip!"

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
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR l u lt Tip | height lt <= 1 = fork l u lt Tip
balanceR _ _ _ Tip = error "Left should have shrank, but is still 1 taller than a Tip!"

{-# INLINE rotr #-}
rotr :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotr l1 u1 (Fork _ l2 u2 p q) r = fork l2 u2 p (fork l1 u1 q r)
rotr _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: a -> a -> RangeSet a -> RangeSet a -> RangeSet a
rotl l1 u1 p (Fork _ l2 u2 q r) = fork l2 u2 (fork l1 u1 p q) r
rotl _ _ _ _ = error "rotr on Tip"

-- TODO: This can be /much much/ better
union :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
union t = foldr insert t . elems

-- TODO: This can be /much much/ better
intersection :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
intersection t = fromList . filter (flip member t) . elems

-- TODO: This can be /much much/ better
difference :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
difference t = foldr delete t . elems

elems :: Enum a => RangeSet a -> [a]
elems t = foldRangeSet (\l u lt rt -> lt . (range l u ++) . rt) id t []

-- TODO: This can be /much much/ better
fromRanges :: (Enum a, Ord a) => [(a, a)] -> RangeSet a
fromRanges = fromList . concatMap (uncurry range)

insertRange :: (Enum a, Ord a) => (a, a) -> RangeSet a -> RangeSet a
insertRange = union . fromRanges . pure

fromList :: (Enum a, Ord a) => [a] -> RangeSet a
fromList = foldr insert empty

foldRangeSet :: (a -> a -> b -> b -> b) -> b -> RangeSet a -> b
foldRangeSet _ tip Tip = tip
foldRangeSet fork tip (Fork _ l u lt rt) = fork l u (foldRangeSet fork tip lt) (foldRangeSet fork tip rt)

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