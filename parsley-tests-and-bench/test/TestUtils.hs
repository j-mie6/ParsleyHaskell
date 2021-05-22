{-# LANGUAGE TemplateHaskell, TypeApplications, DeriveAnyClass, StandaloneDeriving, CPP #-}
module TestUtils where

import Parsley (runParser, Parser, Code)
--import Parsley.Internal.Verbose ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TestUtils
import Language.Haskell.TH.TestUtils.QMode
import Control.DeepSeq

#if __GLASGOW_HASKELL__ >= 810
import GHC.ForeignPtr
#endif

-- TODO Use WQ: requires lift plugin to not require any Lift instance for variables (if missing)
runParserMocked :: Parser a -> Code (Parser a) -> Code (String -> Maybe a)
runParserMocked p qp = [|| \s ->
    runParserMocked' $$qp `deepseq` $$(runParser p) s
  ||]

runParserMocked' :: Parser a -> Exp
runParserMocked' = runTestQ (QState MockQ [] []) . unTypeQ . runParser @String

deriving instance NFData Exp
deriving instance NFData Name
deriving instance NFData OccName
deriving instance NFData NameFlavour
deriving instance NFData ModName
deriving instance NFData NameSpace
deriving instance NFData PkgName
deriving instance NFData Lit
#if __GLASGOW_HASKELL__ >= 810
deriving instance NFData Bytes
instance NFData (ForeignPtr a) where rnf = rwhnf
#endif
deriving instance NFData Type
deriving instance NFData TyVarBndr
deriving instance NFData Pat
deriving instance NFData TyLit
deriving instance NFData Match
deriving instance NFData Body
deriving instance NFData Guard
deriving instance NFData Stmt
deriving instance NFData Dec
deriving instance NFData Clause
deriving instance NFData Con
deriving instance NFData Bang
deriving instance NFData SourceUnpackedness
deriving instance NFData SourceStrictness
deriving instance NFData DerivClause
deriving instance NFData Range
deriving instance NFData DerivStrategy
deriving instance NFData FunDep
deriving instance NFData Overlap
deriving instance NFData Foreign
deriving instance NFData Callconv
deriving instance NFData Fixity
deriving instance NFData FixityDirection
deriving instance NFData Safety
deriving instance NFData Pragma
deriving instance NFData Inline
deriving instance NFData TySynEqn
deriving instance NFData RuleMatch
deriving instance NFData TypeFamilyHead
deriving instance NFData FamilyResultSig
deriving instance NFData Phases
deriving instance NFData Role
deriving instance NFData InjectivityAnn
deriving instance NFData RuleBndr
deriving instance NFData PatSynArgs
deriving instance NFData AnnTarget
deriving instance NFData PatSynDir