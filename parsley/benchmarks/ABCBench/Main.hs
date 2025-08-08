{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module Main where
import Gauge.Main          (Benchmark, bgroup)
import Control.DeepSeq     (NFData)
import GHC.Generics        (Generic)
import Data.ByteString     (ByteString)
import Data.Text           (Text)

import qualified ABCBench.Parsley.Parser
import qualified ABCBench.Gigaparsec.Parser
import qualified Text.Gigaparsec as Gigaparsec

import qualified Parsley

import Shared.BenchmarkUtils
import Data.Maybe (Maybe(Nothing))

main :: IO ()
main = condensedMain [abc]

abcParsleyS :: String -> Maybe ()
abcParsleyS = $$(Parsley.parse ABCBench.Parsley.Parser.abc) 

abcLookAheadParsleyS :: String -> Maybe ()
abcLookAheadParsleyS = $$(Parsley.parse ABCBench.Parsley.Parser.abcPEG)

gigaparsecParse :: Gigaparsec.Parsec () -> String -> Maybe ()
gigaparsecParse p inp = case Gigaparsec.parse @() p inp of 
    Gigaparsec.Failure _ -> Nothing
    Gigaparsec.Success a -> Just a

abc :: Benchmark
abc =
  let test :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe ()) -> Benchmark
      test = benchmark ["benchmarks/inputs/abc_" ++ (show n) ++ ".txt" | n <- [1..20]]
  in bgroup "ABC"
       [ test string "Parsley (String)"               abcParsleyS
       , test string "Parsley lookAhead (String)"     abcLookAheadParsleyS
       , test string "Gigaparsec (String)"            (gigaparsecParse ABCBench.Gigaparsec.Parser.abc)
       , test string "Gigaparsec Ref (String)"        (gigaparsecParse ABCBench.Gigaparsec.Parser.abcWithRef)
       , test string "Gigaparsec lookAhead (String)"  (gigaparsecParse ABCBench.Gigaparsec.Parser.abcPEG)
       ]
