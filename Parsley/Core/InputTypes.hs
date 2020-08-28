module Parsley.Core.InputTypes (module Parsley.Core.InputTypes) where

import Data.Text (Text)

{- Input Types -}
newtype Text16 = Text16 Text
--newtype CacheText = CacheText Text
newtype TokList t = TokList [t]
data Stream = {-# UNPACK #-} !Char :> Stream

nomore :: Stream
nomore = '\0' :> nomore