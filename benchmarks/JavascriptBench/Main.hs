{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module Main where
import Criterion.Main         (Benchmark, bgroup, defaultMain)
import Control.DeepSeq        (NFData)
import GHC.Generics           (Generic)
import Data.Text              (Text)
--import Parsley.Internal.Verbose ()
import qualified JavascriptBench.Parsley.Parser
import qualified JavascriptBench.Parsec.Parser
import qualified JavascriptBench.Megaparsec.Parser
import qualified JavascriptBench.Attoparsec.Parser
import qualified JavascriptBench.Happy.Parser
import qualified Parsley
import JavascriptBench.Shared
import Shared.BenchmarkUtils

main :: IO ()
main = defaultMain [javascript]

deriving instance Generic JSElement
deriving instance Generic JSStm
deriving instance Generic JSVar
deriving instance Generic JSExpr'
deriving instance Generic JSUnary
deriving instance Generic JSMember
deriving instance Generic JSCons
deriving instance Generic JSAtom
deriving instance NFData JSElement
deriving instance NFData JSStm
deriving instance NFData JSVar
deriving instance NFData JSExpr'
deriving instance NFData JSUnary
deriving instance NFData JSMember
deriving instance NFData JSCons
deriving instance NFData JSAtom

javascriptParsleyS :: String -> Maybe JSProgram
javascriptParsleyS = $$(Parsley.runParser JavascriptBench.Parsley.Parser.javascript)

javascriptParsleyT :: Text -> Maybe JSProgram
javascriptParsleyT = $$(Parsley.runParser JavascriptBench.Parsley.Parser.javascript)

javascript :: Benchmark
javascript =
  let jsTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe JSProgram) -> Benchmark
      jsTest = benchmark ["benchmarks/inputs/fibonacci.js", "benchmarks/inputs/heapsort.js", "benchmarks/inputs/game.js", "benchmarks/inputs/big.js"]
  in bgroup "Javascript"
       [ jsTest text   "Parsley (Text)"       javascriptParsleyT
       , jsTest string "Parsley (String)"     javascriptParsleyS
       , jsTest text   "Atto"                 (attoParse JavascriptBench.Attoparsec.Parser.javascript)
       , jsTest string "Happy"                (JavascriptBench.Happy.Parser.runParser JavascriptBench.Happy.Parser.javascript)
       , jsTest string "Parsec (String)"      (parsecParse JavascriptBench.Parsec.Parser.javascript)
       , jsTest text   "Parsec (Text)"        (parsecParse JavascriptBench.Parsec.Parser.javascript)
       , jsTest string "Mega (String)"        (megaParse JavascriptBench.Megaparsec.Parser.javascript)
       , jsTest text   "Mega (Text)"          (megaParse JavascriptBench.Megaparsec.Parser.javascript)
       ]