{-|
Module      : Parsley.Internal.Frontend.Analysis
Description : Exposes various analysis passes.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the analysis passes defined within the analysis submodules via `analyse`.

@since 1.5.0.0
-}
module Parsley.Internal.Frontend.Analysis (
    analyse, dependencyAnalysis,
    module Flags
  ) where

import Parsley.Internal.Common.Indexed                 (Fix)
import Parsley.Internal.Core.CombinatorAST             (Combinator)
import Parsley.Internal.Frontend.Analysis.Cut          (cutAnalysis)
import Parsley.Internal.Frontend.Analysis.Dependencies (dependencyAnalysis)

import Parsley.Internal.Frontend.Analysis.Flags as Flags (emptyFlags, AnalysisFlags)

{-|
Performs Cut-Analysis on the combinator tree (See "Parsley.Internal.Frontend.Analysis.Cut")

@since 1.5.0.0
-}
analyse :: AnalysisFlags -> Fix Combinator a -> Fix Combinator a
analyse _ = cutAnalysis