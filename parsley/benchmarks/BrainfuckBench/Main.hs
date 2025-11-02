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
import BrainfuckBench.Shared
import Shared.BenchmarkUtils

import qualified BrainfuckBench.Parsec.Parser
import qualified BrainfuckBench.Megaparsec.Parser
import qualified BrainfuckBench.Attoparsec.Parser
import qualified BrainfuckBench.Handrolled.Parser
import qualified BrainfuckBench.Happy.Parser
import qualified Parsley
import qualified Data.ByteString.Lazy
import qualified BrainfuckBench.Parsley.Parser

main :: IO ()
main = condensedMain [brainfuck]

deriving instance Generic BrainFuckOp

brainfuckParsleyS :: String -> Maybe [BrainFuckOp]
brainfuckParsleyS = $$(Parsley.parse BrainfuckBench.Parsley.Parser.brainfuck')

brainfuckParsleyT :: Text -> Maybe [BrainFuckOp]
brainfuckParsleyT = $$(Parsley.parse BrainfuckBench.Parsley.Parser.brainfuck')

brainfuckParsleyB :: ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyB = $$(Parsley.parse BrainfuckBench.Parsley.Parser.brainfuck')

brainfuckParsleyLB :: Data.ByteString.Lazy.ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyLB = $$(Parsley.parse BrainfuckBench.Parsley.Parser.brainfuck')

brainfuckParsleySTwoLoops :: String -> Maybe [BrainFuckOp]
brainfuckParsleySTwoLoops = $$(Parsley.parse BrainfuckBench.Parsley.Parser.twoLoops)

brainfuckParsleySTwoLoops' :: String -> Maybe [BrainFuckOp]
brainfuckParsleySTwoLoops' = $$(Parsley.parse BrainfuckBench.Parsley.Parser.twoLoops')

brainfuckParsleySOneMaybe :: String -> Maybe [BrainFuckOp]
brainfuckParsleySOneMaybe = $$(Parsley.parse BrainfuckBench.Parsley.Parser.oneLoopMaybe) 

brainfuckParsleySOneRec :: String -> Maybe [BrainFuckOp]
brainfuckParsleySOneRec = $$(Parsley.parse BrainfuckBench.Parsley.Parser.oneRecursive)

brainfuckParsleySOneReg :: String -> Maybe [BrainFuckOp]
brainfuckParsleySOneReg = $$(Parsley.parse BrainfuckBench.Parsley.Parser.oneLoopReg)

brainfuckParsleySOneReg' :: String -> Maybe [BrainFuckOp]
brainfuckParsleySOneReg' = $$(Parsley.parse BrainfuckBench.Parsley.Parser.oneLoopReg') 

brainfuck :: Benchmark
brainfuck =
  let bfTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe [BrainFuckOp]) -> Benchmark
      bfTest = benchmark ["benchmarks/inputs/helloworld.bf", "benchmarks/inputs/helloworld_golfed.bf", "benchmarks/inputs/compiler.bf"]
  in bgroup "Brainfuck"
       [ bfTest string          "Parsley (String)"          brainfuckParsleyS
       , bfTest string          "Parsley (two loops)"       brainfuckParsleySTwoLoops
       , bfTest string          "Parsley (two loops prime)" brainfuckParsleySTwoLoops'
       , bfTest string          "Parsley (one maybe)"       brainfuckParsleySOneMaybe
       , bfTest string          "Parsley (one rec)"         brainfuckParsleySOneRec
       , bfTest string          "Parsley (one reg)"         brainfuckParsleySOneReg
       , bfTest string          "Parsley (one reg prime)"   brainfuckParsleySOneReg'
       -- , bfTest text            "Parsley (Text)"            brainfuckParsleyT
       -- , bfTest bytestring      "Parsley (ByteString)"      brainfuckParsleyB
       -- , bfTest lazy_bytestring "Parsley (Lazy ByteString)" brainfuckParsleyLB
       -- , bfTest string          "Handrolled"                BrainfuckBench.Handrolled.Parser.brainfuck
       -- , bfTest string          "Happy"                     BrainfuckBench.Happy.Parser.brainfuck
       -- , bfTest string          "Parsec (String)"           (parsecParse BrainfuckBench.Parsec.Parser.brainfuck)
       -- , bfTest text            "Parsec (Text)"             (parsecParse BrainfuckBench.Parsec.Parser.brainfuck)
       -- , bfTest string          "Mega (String)"             (megaParse BrainfuckBench.Megaparsec.Parser.brainfuck)
       -- , bfTest text            "Mega (Text)"               (megaParse BrainfuckBench.Megaparsec.Parser.brainfuck)
       -- , bfTest text            "Atto (Text)"               (attoParse BrainfuckBench.Attoparsec.Parser.brainfuck)
       ]
