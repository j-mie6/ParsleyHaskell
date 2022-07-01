{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Input.Pos
Description : Packaging of offsets and positions.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the machinery for manipulating position information, both in static and dynamic
forms.

@since 2.1.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos, fromStaPos,
    force, update
  ) where

import Data.Bits                               ((.|.))
import Data.List                               (foldl')
import Parsley.Internal.Common.Utils           (Code)
import Parsley.Internal.Core.CharPred          (CharPred, pattern Specific, apply)
import Parsley.Internal.Core.CombinatorAST     (PosSelector(..))
import Parsley.Internal.Backend.Machine.PosOps (liftPos)

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

{-|
The type-alias for dynamic positions.

@since 2.1.0.0
-}
type DynPos = Code Base.Pos

{-|
Type that represents static positions and their associated data.

@since 2.1.0.0
-}
data StaPos = StaPos {
    dynPos :: !Pos,
    alignment :: !Alignment,
    contributing :: ![StaChar]
  }

{-|
Converts a dynamic position into an unannotated static one.

@since 2.1.0.0
-}
fromDynPos :: DynPos -> StaPos
fromDynPos = mkStaPos . Dynamic

{-|
Forgets the static information found in a position and converts it into a dynamic one.

@since 2.1.0.0
-}
toDynPos :: StaPos -> DynPos
toDynPos = fromPos . collapse

{-|
Produce a static position from a given line and column pair.

@since 2.1.0.0
-}
fromStaPos :: (Word, Word) -> StaPos
fromStaPos = mkStaPos . uncurry Static

{-|
Given a static position, and a component to select, collapse the position down to its smallest form
(binding this to a let if necessary) and extract the desired component. The new, potentially rebound,
position is provided to the continuation too.

@since 2.1.0.0
-}
force :: StaPos -> PosSelector -> (Code Int -> StaPos -> Code r) -> Code r
force p sel k
  | null (contributing p) = k (extract sel (dynPos p)) p
  | otherwise = case collapse p of
    p'@Static{} -> k (extract sel p') (newPos p')
    Dynamic qpos -> [||
        let pos = $$qpos
        in $$(k (extract sel (Dynamic [||pos||])) (newPos (Dynamic [||pos||])))
      ||]
  where
    newPos pos = StaPos {
      dynPos = pos,
      alignment = updateAlignment (contributing p) (alignment p),
      contributing = []
    }
    extract Line (Dynamic pos) = Ops.extractLine pos
    extract Line (Static line _) = let line' = fromEnum line in [||line'||]
    extract Col (Dynamic pos) = Ops.extractCol pos
    extract Col (Static _ col) = let col' = fromEnum col in [||col'||]

{-|
Advance a static position accounting for the dynamic character that was last read and the
static predicate that guarded that read.

@since 2.1.0.0
-}
update :: StaPos -> Code Char -> CharPred -> StaPos
update pos c p = pos { contributing = StaChar c p : contributing pos }

{-----------------}
{-   INTERNALS   -}
{-----------------}

-- Data

-- TODO: This could be more fine-grained, for instance a partially static position.
data Pos = Static {-# UNPACK #-} !Word {-# UNPACK #-} !Word | Dynamic DynPos

data Alignment = Unknown | Unaligned {-# UNPACK #-} !Word

pattern Aligned :: Alignment
pattern Aligned = Unaligned 0

data StaChar = StaChar {
    char :: !(Code Char),
    predicate :: !CharPred
  }

data CharClass = Tab | Newline | Regular | NonNewline

data Updater = DynUpdater !DynUpdater !(Code Char)
             | StaUpdater !StaUpdater

data StaUpdater = OffsetLineAndSetCol {-# UNPACK #-} !Word {-# UNPACK #-} !Word
                | OffsetCol {-# UNPACK #-} !Word
                | OffsetAlignOffsetCol {-# UNPACK #-} !Word {-# UNPACK #-} !Word

data DynUpdater = FullUpdate
                | NoNewlineUpdate
                | NoColUpdate

-- Functions

mkStaPos :: Pos -> StaPos
mkStaPos pos = StaPos { dynPos = pos, alignment = alignment pos, contributing = [] }
  where
    alignment Dynamic{} = Unknown
    alignment (Static _ col) = Unaligned (col - 1 `mod` Ops.tabWidth)

fromPos :: Pos -> DynPos
fromPos (Static l c) = liftPos l c
fromPos (Dynamic p) = p

updateAlignment :: [StaChar] -> Alignment -> Alignment
updateAlignment cs a = foldr (updateAlignment' . knownChar . predicate) a cs
  where
    updateAlignment' Nothing           _             = Unknown
    updateAlignment' (Just Regular)    (Unaligned n) = Unaligned (n + 1 `mod` Ops.tabWidth)
    updateAlignment' (Just Regular)    Unknown       = Unknown
    updateAlignment' (Just NonNewline) _             = Unknown
    updateAlignment' _                 _             = Aligned

collapse :: StaPos -> Pos
collapse StaPos{..} = applyUpdaters dynPos (buildUpdaters alignment contributing)

updateTab :: Maybe StaUpdater -> StaUpdater
updateTab Nothing = OffsetAlignOffsetCol 0 0
updateTab (Just (OffsetLineAndSetCol n m)) = OffsetLineAndSetCol n (Ops.toNextTab m)
updateTab (Just (OffsetCol n)) = OffsetAlignOffsetCol n 0
updateTab (Just (OffsetAlignOffsetCol firstBy thenBy)) = OffsetAlignOffsetCol firstBy (toNextTabFromKnownAlignment thenBy)

updateRegular :: Maybe StaUpdater -> StaUpdater
updateRegular Nothing = OffsetCol 1
updateRegular (Just (OffsetLineAndSetCol n m)) = OffsetLineAndSetCol n (m + 1)
updateRegular (Just (OffsetCol n)) = OffsetCol (n + 1)
updateRegular (Just (OffsetAlignOffsetCol firstBy thenBy)) = OffsetAlignOffsetCol firstBy (thenBy + 1)

updateNewline :: Maybe StaUpdater -> StaUpdater
updateNewline (Just (OffsetLineAndSetCol n _)) = OffsetLineAndSetCol (n + 1) 1
updateNewline _ = OffsetLineAndSetCol 1 1

toNextTabFromKnownAlignment :: Word -> Word
toNextTabFromKnownAlignment x = (x .|. Ops.tabWidth - 1) + 1

{-| Takes the initial alignment and contributing characters and
    return the list of updaters (in order from left-to-right)
    that must be applied to update the position properly -}
buildUpdaters :: Alignment -> [StaChar] -> [Updater]
buildUpdaters alignment = applyAlignment alignment . removeDeadUpdates . uncurry combine . foldr f (Nothing, [])
  where
    -- The known initial alignment can affect the /first/ updater
    applyAlignment :: Alignment -> [Updater] -> [Updater]
    applyAlignment (Unaligned n) (StaUpdater (OffsetAlignOffsetCol firstBy thenBy) : updaters) =
      -- We know what the current alignment boundary is, so can eliminate the Align
      let pre = n + firstBy
          nextTabIn = toNextTabFromKnownAlignment pre
      in StaUpdater (OffsetCol (nextTabIn + thenBy)) : updaters
    applyAlignment _ updaters = updaters

    combine :: Maybe StaUpdater -> [Updater] -> [Updater]
    combine Nothing updaters = updaters
    combine (Just updater) updaters = StaUpdater updater : updaters

    f :: StaChar -> (Maybe StaUpdater, [Updater]) -> (Maybe StaUpdater, [Updater])
    f StaChar{..} (updater, updaters) =
      let charClass = knownChar predicate
      in case charClass of
        Just Tab        -> (Just (updateTab updater), updaters)
        Just Newline    -> (Just (updateNewline updater), updaters)
        Just Regular    -> (Just (updateRegular updater), updaters)
        Just NonNewline -> (Nothing, DynUpdater NoNewlineUpdate char : combine updater updaters)
        _               -> (Nothing, DynUpdater FullUpdate char : combine updater updaters)

    -- This function should reverse the list, and also remove any redundant updaters:
    -- when a newline is known, any updater before it is only useful for the newlines.
    removeDeadUpdates :: [Updater] -> [Updater]
    removeDeadUpdates = fst . foldl' g ([], True)
      where
        g :: ([Updater], Bool) -> Updater -> ([Updater], Bool)
        g res@(updaters, keep) updater@(DynUpdater kind c)
          | keep                              = (updater : updaters, True)
          -- If we're dropping because of lines, then a dynamic update known not to affect lines isn't needed
          | not keep, NoNewlineUpdate <- kind = res
          -- If we're dropping because of lines, then we don't need column updates
          | otherwise                         = (DynUpdater NoColUpdate c : updaters, False)
        -- This is a line updater, no tab or regular updaters matter anymore
        g (updaters, _) updater@(StaUpdater OffsetLineAndSetCol{}) = (updater : updaters, False)
        -- This a static non-line related update, we can drop it if needed
        g res@(updaters, keep) updater@StaUpdater{}
          | keep      = (updater : updaters, True)
          | otherwise = res

applyUpdaters :: Pos -> [Updater] -> Pos
applyUpdaters = foldl' applyUpdater
  where
    applyUpdater (Static line _) (DynUpdater NoColUpdate c) = Dynamic (Ops.updatePosNewlineOnly c line)
    applyUpdater (Dynamic pos) (DynUpdater NoColUpdate c)   = Dynamic (Ops.updatePosNewlineOnlyQ c pos)
    applyUpdater (Static line col) (DynUpdater _ c)         = Dynamic (Ops.updatePos c line col)
    applyUpdater (Dynamic pos) (DynUpdater _ c)             = Dynamic (Ops.updatePosQ c pos)
    applyUpdater pos (StaUpdater updater)                   = applyStaUpdater pos updater

    applyStaUpdater (Static line _)   (OffsetLineAndSetCol n m)             = uncurry Static $ Ops.shiftLineAndSetCol n m line
    applyStaUpdater (Static line col) (OffsetCol n)                         = uncurry Static $ Ops.shiftCol n line col
    applyStaUpdater (Static line col) (OffsetAlignOffsetCol firstBy thenBy) = uncurry Static $ Ops.shiftAlignAndShiftCol firstBy thenBy line col
    applyStaUpdater (Dynamic pos)     (OffsetLineAndSetCol n m)             = Dynamic $ Ops.shiftLineAndSetColQ n m pos
    applyStaUpdater (Dynamic pos)     (OffsetCol n)                         = Dynamic $ Ops.shiftColQ n pos
    applyStaUpdater (Dynamic pos)     (OffsetAlignOffsetCol firstBy thenBy) = Dynamic $ Ops.shiftAlignAndShiftColQ firstBy thenBy pos

knownChar :: CharPred -> Maybe CharClass
knownChar (Specific '\t')         = Just Tab
knownChar (Specific '\n')         = Just Newline
knownChar p | not (apply p '\n')  = Just $ if not (apply p '\t') then Regular else NonNewline
knownChar _                       = Nothing
