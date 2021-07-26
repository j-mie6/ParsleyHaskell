module Parsley.Internal.Frontend.Analysis.Flags (AnalysisFlags(letBound), emptyFlags) where

newtype AnalysisFlags = AnalysisFlags {
  letBound :: Bool
}
emptyFlags :: AnalysisFlags
emptyFlags = AnalysisFlags False