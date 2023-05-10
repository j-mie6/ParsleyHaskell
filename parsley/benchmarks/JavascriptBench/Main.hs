{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module Main where
import Gauge.Main      (Benchmark, bgroup)
import Control.DeepSeq (NFData)
import GHC.Generics    (Generic)
import Data.Text       (Text)
import Data.ByteString (ByteString)
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
main = do
  print (javascriptParsleyS "function foo(x) { return x; }")
  condensedMain [javascript]

javascriptParsleyS :: String -> Maybe JSProgram
javascriptParsleyS = $$(Parsley.parse JavascriptBench.Parsley.Parser.javascript)

javascriptParsleyT :: Text -> Maybe JSProgram
javascriptParsleyT = $$(Parsley.parse JavascriptBench.Parsley.Parser.javascript)

javascriptParsleyB :: ByteString -> Maybe JSProgram
javascriptParsleyB= $$(Parsley.parse JavascriptBench.Parsley.Parser.javascript)

javascript :: Benchmark
javascript =
  let jsTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe JSProgram) -> Benchmark
      jsTest = benchmark ["benchmarks/inputs/fibonacci.js", "benchmarks/inputs/heapsort.js", "benchmarks/inputs/game.js", "benchmarks/inputs/big.js"]
  in bgroup "Javascript"
       [ jsTest text       "Parsley (Text)"       javascriptParsleyT
       , jsTest string     "Parsley (String)"     javascriptParsleyS
       , jsTest bytestring "Parsley (ByteString)" javascriptParsleyB
       , jsTest text       "Atto"                 (attoParse JavascriptBench.Attoparsec.Parser.javascript)
       , jsTest string     "Happy"                (JavascriptBench.Happy.Parser.runParser JavascriptBench.Happy.Parser.javascript)
       , jsTest string     "Parsec (String)"      (parsecParse JavascriptBench.Parsec.Parser.javascript)
       , jsTest text       "Parsec (Text)"        (parsecParse JavascriptBench.Parsec.Parser.javascript)
       , jsTest string     "Mega (String)"        (megaParse JavascriptBench.Megaparsec.Parser.javascript)
       , jsTest text       "Mega (Text)"          (megaParse JavascriptBench.Megaparsec.Parser.javascript)
       ]
