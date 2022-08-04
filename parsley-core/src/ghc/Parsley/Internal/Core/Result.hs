{-|
Module      : Parsley.Internal.Core.Result
Description : Result type for parsers.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

@since 1.0.1.0
-}
module Parsley.Internal.Core.Result (Result(..), toMaybe{-, toEither-}) where

data Result err a = Success a | Failure {-err-}

toMaybe :: Result err a -> Maybe a
toMaybe (Success x) = Just x
toMaybe Failure{} = Nothing

{-toEither :: Result err a -> Either err a
toEither (Success x) = Right x
toEither (Failure msg) = Left msg-}
