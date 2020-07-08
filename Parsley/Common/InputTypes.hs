module Parsley.Common.InputTypes where

import Data.Text (Text)

{- Input Types -}
newtype Text16 = Text16 Text
--newtype CacheText = CacheText Text
newtype CharList = CharList String
data Stream = {-# UNPACK #-} !Char :> Stream

nomore :: Stream
nomore = '\0' :> nomore