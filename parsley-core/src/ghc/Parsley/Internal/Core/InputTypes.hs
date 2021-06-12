module Parsley.Internal.Core.InputTypes (module Parsley.Internal.Core.InputTypes) where

import Data.Text (Text)

{-|
By wrapping a regular @Text@ input with this newtype, Parsley will assume that all
of the characters fit into exactly one 16-bit chunk. This allows the consumption of
characters in the datatype to be consumed much faster, but does not support multi-word
characters. 

@since 0.1.0.0
-}
newtype Text16 = Text16 Text

--newtype CacheText = CacheText Text

{-|
By wrapping a regular @String@ with this newtype, Parsley will not preprocess it into
an array of characters, instead using regular pattern matching for the implementation.

@since 0.1.0.0
-}
newtype CharList = CharList String

{-|
An input type that represents an infinite stream of input characters.

@since 0.1.0.0
-}
data Stream = {-# UNPACK #-} !Char :> Stream

{-|
The \"end\" of a stream, an infinite stream of \'\\0\' (null) characters

@since 0.1.0.0
-}
nomore :: Stream
nomore = '\0' :> nomore