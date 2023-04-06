{-# LANGUAGE UnboxedTuples, DerivingStrategies, DeriveLift #-}
{-# OPTIONS_GHC -Wno-partial-fields -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Unused LANGUAGE pragma" #-}
module Parsley.Internal.Backend.Machine.Types.Errors.Defunc (DefuncGhosts(..), size, DefuncError, pos, offset, mergeErrors, withGhosts, withReason, label, amend, entrench, isExpectedEmpty, classicExpectedError, emptyError, classicUnexpectedError, classicFancyError, mergeGhosts, pop, rename, addGhost) where

import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Backend.Machine.Types.Errors.ErrorItem (ErrorItem)
import Data.Word (Word8)
import Data.Bits (Bits((.&.), testBit, setBit, clearBit, zeroBits))
import Language.Haskell.TH.Syntax (Lift)

-- We still want to defunctionalise the ghosts mechanism, because it allows us to both inspect
-- the error in-flight, as well as collapse it in an efficient way.
-- This might change, however

-- In fact, I /suspect/ that we want the ghosts machinery here to be static, and then collapse
-- it into a dynamic structure when we cross the dynamic boundary.

data DefuncGhosts where
  EmptyGhosts :: DefuncGhosts
  PopGhost :: {-# UNPACK #-} !Int -> DefuncGhosts -> DefuncGhosts
  ReplaceLabel :: {-# UNPACK #-} !Int -> String -> DefuncGhosts -> DefuncGhosts
  MergeGhosts :: {-# UNPACK #-} !Int -> DefuncGhosts -> DefuncGhosts -> DefuncGhosts
  AddGhost :: {-# UNPACK #-} !Int -> DefuncGhosts -> DefuncError -> DefuncGhosts
  deriving stock (Lift{-, Eq-}, Show)

size :: DefuncGhosts -> Int
size EmptyGhosts = 0
size (PopGhost sz _) = sz
size (ReplaceLabel sz _ _) = sz
size (MergeGhosts sz _ _) = sz
size (AddGhost sz _ _) = sz

isEmpty :: DefuncGhosts -> Bool
--isEmpty = (== 0) . size
isEmpty EmptyGhosts = True
isEmpty _           = False

type Flags = Word8

{-# INLINE setBitTo #-}
setBitTo :: Bool -> Int -> Flags -> Flags
setBitTo True !bit !flags = setBit flags bit
setBitTo False bit flags = clearBit flags bit

{-# INLINE _flags #-}
_flags :: Bool -> Bool -> Bool -> Flags
_flags isTrivial isExpectedEmpty entrenched =
  setBitTo isTrivial 0 $
  setBitTo isExpectedEmpty 1 $
  setBitTo entrenched 2 zeroBits

{-# INLINE _andFlags #-}
_andFlags :: Flags -> Flags -> Flags
_andFlags !flags1 !flags2 = flags1 .&. flags2

{-# INLINE _isTrivial #-}
_isTrivial :: Flags -> Bool
_isTrivial !flags = testBit flags 0

{-# INLINE _isExpectedEmpty #-}
_isExpectedEmpty :: Flags -> Bool
_isExpectedEmpty !flags = testBit flags 1

{-# INLINE _setExpectedEmpty #-}
_setExpectedEmpty :: Bool -> Flags -> Flags
_setExpectedEmpty b !flags = setBitTo b 1 flags

{-# INLINE _entrenched #-}
_entrenched :: Flags -> Bool
_entrenched !flags = testBit flags 2

{-# INLINE _setEntrenched #-}
_setEntrenched :: Flags -> Flags
_setEntrenched !flags = setBit flags 2

{-# INLINE isTrivial #-}
isTrivial :: DefuncError -> Bool
isTrivial = _isTrivial . flags

{-# INLINE isExpectedEmpty #-}
isExpectedEmpty :: DefuncError -> Bool
isExpectedEmpty = _isExpectedEmpty . flags

{-# INLINE entrenched #-}
entrenched :: DefuncError -> Bool
entrenched = _entrenched . flags

-- TODO: I think these need to changed to reflect the 6 kinds of error generated:
--         EmptyError - from empty
--         UnexpectedError - from unexpected
--         FancyError - from fail
--         EndOfInputError - from failed `more` check
--         NotEnoughInputError - from failed input check (with n >= 2) (this has a multi-width unexpected token!)
--         InvalidTokenError - from failed `sat` check
data DefuncError where
  EmptyError                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos } -> DefuncError
  ClassicExpectedError           :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _expected :: !(Maybe ErrorItem) } -> DefuncError
  ClassicUnexpectedError         :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _unexpected :: !ErrorItem } -> DefuncError
  ClassicFancyError              :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _msgs :: ![String] } -> DefuncError
  MergedErrors                   :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err1 :: !DefuncError, _err2 :: !DefuncError } -> DefuncError
  WithGhosts                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _ghosts :: !DefuncGhosts } -> DefuncError
  WithReason                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _reason :: !String } -> DefuncError
  WithLabel                      :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _label :: !String } -> DefuncError
  Amended                        :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError } -> DefuncError
  Entrenched                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError } -> DefuncError
  deriving stock Lift

-- Smart Constructors
emptyError :: Int -> Pos -> DefuncError
emptyError = EmptyError (_flags True True False)

classicExpectedError :: Maybe ErrorItem -> Int -> Pos -> DefuncError
classicExpectedError Nothing !offset !pos = ClassicExpectedError (_flags True True False) offset pos Nothing
classicExpectedError item offset pos = ClassicExpectedError (_flags True False False) offset pos item

classicUnexpectedError :: ErrorItem -> Int -> Pos -> DefuncError
classicUnexpectedError !unexpected !offset !pos = ClassicUnexpectedError (_flags True True False) offset pos unexpected

classicFancyError :: [String] -> Int -> Pos -> DefuncError
classicFancyError !msgs !offset !pos = ClassicFancyError (_flags False True False)  offset pos msgs

-- Operations
mergeErrors :: DefuncError -> DefuncError -> DefuncError
mergeErrors !err1 !err2 = case compare (offset err1) (offset err2) of
  GT -> err1
  LT -> err2
  EQ | trivial1 == trivial2 -> MergedErrors (_andFlags (flags err1) (flags err2)) (offset err1) err1 err2
     | trivial1             -> err2
     | otherwise            -> err1
  where
    trivial1 = isTrivial err1
    trivial2 = isTrivial err2

withGhosts :: DefuncError -> DefuncGhosts -> DefuncError
withGhosts !err !ghosts
  | isTrivial err, not (isEmpty ghosts) = WithGhosts (_setExpectedEmpty False (flags err)) (offset err) err ghosts
  | otherwise = err

withReason :: DefuncError -> String -> DefuncError
withReason !err !reason
  | isTrivial err = WithReason (flags err) (offset err) err reason
  | otherwise = err

label :: DefuncError -> String -> Int -> DefuncError
label !err !l !off
  | isTrivial err, offset err == off = WithLabel (_setExpectedEmpty (null l) (flags err)) off err l
  | otherwise                        = err

amend :: DefuncError -> Int -> DefuncError
amend !err !off
  | entrenched err = err
  | otherwise = Amended (flags err) off err

entrench :: DefuncError -> DefuncError
entrench !err
  | entrenched err = err
  | otherwise = Entrenched (_setEntrenched (flags err)) (offset err) err

mergeGhosts :: DefuncGhosts -> DefuncGhosts -> DefuncGhosts
mergeGhosts !g1 !g2
  | isEmpty g1 = g2
  | isEmpty g2 = g1
  | otherwise = MergeGhosts (size g1 + size g2) g1 g2

pop :: DefuncGhosts -> DefuncGhosts
pop !ghosts
  | sz  > 1 = PopGhost (sz - 1) ghosts
  | otherwise = EmptyGhosts
  where
    !sz = size ghosts

rename :: DefuncGhosts -> String -> DefuncGhosts
rename !ghosts !l
  | not (isEmpty ghosts) = ReplaceLabel (size ghosts) l ghosts
  | otherwise            = ghosts

addGhost :: DefuncGhosts -> DefuncError -> DefuncGhosts
addGhost !ghosts !err
  -- a non-empty expected implies trivial
  {- redundant | {-isTrivial err, -} not (isExpectedEmpty err)-} = AddGhost (size ghosts + 1) ghosts err
  {- redundant | otherwise     = error "only trivial errors will get added to the ghosts"-}

instance Show DefuncError where
  show _ = "TODO"

{-
instance Eq DefuncError where
  (==) = undefined
-}
