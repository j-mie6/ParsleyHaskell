{-# LANGUAGE DeriveLift, DerivingStrategies, UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
module Parsley.Internal.Backend.Machine.Types.Errors.Defunc (DefuncGhosts, size, DefuncError, offset, merge, withGhosts, withReason, label, amend, entrench, isExpectedEmpty, classicExpectedError, emptyError, classicExpectedErrorWithReason, classicUnexpectedError, classicFancyError) where

import Language.Haskell.TH.Syntax (Lift)
import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Backend.Machine.Types.Errors.ErrorItem (ErrorItem)
import Data.Word (Word8)
import Data.Bits (Bits((.&.), testBit, setBit, clearBit, zeroBits))

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
  deriving stock (Lift{-, Eq, Show-})

size :: DefuncGhosts -> Int
size EmptyGhosts = 0
size (PopGhost sz _) = sz
size (ReplaceLabel sz _ _) = sz
size (MergeGhosts sz _ _) = sz
size (AddGhost sz _ _) = sz

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

data DefuncError where
  EmptyError                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos } -> DefuncError
  ClassicExpectedError           :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _expected :: !(Maybe ErrorItem) } -> DefuncError
  ClassicExpectedErrorWithReason :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _expected :: !(Maybe ErrorItem), _reason :: !String } -> DefuncError
  ClassicUnexpectedError         :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _expected :: !(Maybe ErrorItem), _unexpected :: !ErrorItem } -> DefuncError
  ClassicFancyError              :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, pos :: !Pos, _msgs :: ![String] } -> DefuncError
  MergedErrors                   :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err1 :: !DefuncError, _err2 :: !DefuncError } -> DefuncError
  WithGhosts                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _ghosts :: !DefuncGhosts } -> DefuncError
  WithReason                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _reason :: !String } -> DefuncError
  WithLabel                      :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError, _label :: !String } -> DefuncError
  Amended                        :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError } -> DefuncError
  Entrenched                     :: { flags :: {-# UNPACK #-} !Flags, offset :: {-# UNPACK #-} !Int, _err :: !DefuncError } -> DefuncError
  deriving stock (Lift{-, Eq, Show-})

-- Smart Constructors
emptyError :: Int -> Pos -> DefuncError
emptyError = EmptyError (_flags True True False)

classicExpectedError :: Int -> Pos -> Maybe ErrorItem -> DefuncError
classicExpectedError !offset !pos Nothing = ClassicExpectedError (_flags True True False) offset pos Nothing
classicExpectedError offset pos item = ClassicExpectedError (_flags True False False) offset pos item

classicExpectedErrorWithReason :: Int -> Pos -> Maybe ErrorItem -> String -> DefuncError
classicExpectedErrorWithReason !offset !pos Nothing = ClassicExpectedErrorWithReason (_flags True True False) offset pos Nothing
classicExpectedErrorWithReason offset pos item = ClassicExpectedErrorWithReason (_flags True False False) offset pos item

classicUnexpectedError :: Int -> Pos -> Maybe ErrorItem -> ErrorItem -> DefuncError
classicUnexpectedError !offset !pos Nothing = ClassicUnexpectedError (_flags True True False) offset pos Nothing
classicUnexpectedError offset pos item = ClassicUnexpectedError (_flags True False False) offset pos item

classicFancyError :: Int -> Pos -> [String] -> DefuncError
classicFancyError = ClassicFancyError (_flags False True False)

-- Operations
merge :: DefuncError -> DefuncError -> DefuncError
merge err1 err2 = case compare (offset err1) (offset err2) of
  GT -> err1
  LT -> err2
  EQ | trivial1 == trivial2 -> MergedErrors (_andFlags (flags err1) (flags err2)) (offset err1) err1 err2
     | trivial1             -> err2
     | otherwise            -> err1
  where
    trivial1 = isTrivial err1
    trivial2 = isTrivial err2

withGhosts :: DefuncError -> DefuncGhosts -> DefuncError
withGhosts err ghosts
  | isTrivial err, size ghosts /= 0 = WithGhosts (_setExpectedEmpty False (flags err)) (offset err) err ghosts
  | otherwise = err

withReason :: DefuncError -> String -> DefuncError
withReason err reason
  | isTrivial err = WithReason (flags err) (offset err) err reason
  | otherwise = err

label :: DefuncError -> String -> Int -> DefuncError
label err l off
  | isTrivial err, offset err == off = WithLabel (_setExpectedEmpty (null l) (flags err)) off err l
  | otherwise                        = err

amend :: DefuncError -> DefuncError
amend err
  | entrenched err = err
  | otherwise = Amended (flags err) (offset err) err

entrench :: DefuncError -> DefuncError
entrench err
  | entrenched err = err
  | otherwise = Entrenched (_setEntrenched (flags err)) (offset err) err
