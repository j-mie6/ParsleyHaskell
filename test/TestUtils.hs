{-# LANGUAGE TemplateHaskell, GeneralizedNewtypeDeriving, TypeApplications #-}
module TestUtils where

import Parsley (runParser, Parser, Code)
import Parsley.Internal.Verbose ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TestUtils
import Language.Haskell.TH.TestUtils.QMode

-- TODO Use WQ: requires lift plugin to not require any Lift instance for variables (if missing)
runParserMocked :: Parser a -> Code (Parser a) -> Code (String -> Maybe a)
runParserMocked p qp = [|| \s ->
    runParserMocked' $$qp `seq` $$(runParser p) s
  ||]

-- Use DeepSeq instead, the either thing is a mess frankly
runParserMocked' :: Parser a -> ()
runParserMocked' = either error (const ()) . tryTestQ (QState MockQ [] []) . unTypeQ . runParser @String