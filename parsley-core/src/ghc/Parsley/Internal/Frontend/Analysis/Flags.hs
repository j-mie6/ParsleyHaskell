{-|
Module      : Parsley.Internal.Frontend.Analysis.Flags
Description : Flags needed to control analysis.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Contains flags that can control how analysis should proceed.

@since 1.5.0.0
-}
module Parsley.Internal.Frontend.Analysis.Flags (AnalysisFlags(letBound), emptyFlags) where

{-|
The packaged flags object.

@since 1.5.0.0
-}
newtype AnalysisFlags = AnalysisFlags {
  {-|
  Is the binding used in this analysis let-bound?

  @since 1.5.0.0
  -}
  letBound :: Bool
}

{-|
An empty `AnalysisFlags` instance populated with sensible default values.

@since 1.5.0.0
-}
emptyFlags :: AnalysisFlags
emptyFlags = AnalysisFlags False