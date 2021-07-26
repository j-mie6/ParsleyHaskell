module Parsley.Internal.Frontend.Analysis (
    analyse,
    module Flags
  ) where

import Parsley.Internal.Common.Indexed        (Fix)
import Parsley.Internal.Core.CombinatorAST    (Combinator)
import Parsley.Internal.Frontend.Analysis.Cut (cutAnalysis)

import Parsley.Internal.Frontend.Analysis.Flags as Flags (emptyFlags, AnalysisFlags(letBound))

analyse :: AnalysisFlags -> Fix Combinator a -> Fix Combinator a
analyse flags = cutAnalysis (letBound flags)