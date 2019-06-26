{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds, TypeOperators #-}
module Main where
import Criterion.Main  (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq (NFData(rnf))
import GHC.Generics    (Generic)
import qualified ParsleyParsers
import qualified YodaParsers
import qualified ParsecParsers
import qualified MegaparsecParsers
import qualified AttoparsecParsers
import qualified NativeParsers
import qualified Parsley
import qualified Text.Yoda as Yoda
import qualified Text.Parsec as Parsec
import CommonFunctions

import Text.Megaparsec
import Data.Text (Text, pack)
import qualified Data.Text.IO

deriving instance Generic Pred
deriving instance NFData Pred
deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

parsecParseS :: ParsecParsers.Parser String a -> String -> Maybe a
parsecParseS p input = either (const Nothing) Just (Parsec.parse p "" input)

parsecParseT :: ParsecParsers.Parser Text a -> String -> Maybe a
parsecParseT p input = either (const Nothing) Just (Parsec.parse p "" (pack input))

megaParseS :: MegaparsecParsers.Parser String a -> String -> Maybe a
megaParseS = Text.Megaparsec.parseMaybe

megaParseT :: MegaparsecParsers.Parser Text a -> String -> Maybe a
megaParseT p = Text.Megaparsec.parseMaybe p . pack

tailTestP :: String -> Maybe Char
tailTestP = $$(Parsley.runParser ParsleyParsers.phiTest)

brainfuckParsley :: String -> Maybe [BrainFuckOp]
brainfuckParsley = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsley' :: Text -> Maybe [BrainFuckOp]
brainfuckParsley' = $$(Parsley.runParser ParsleyParsers.brainfuck)

tailTest :: Benchmark
tailTest = bgroup "tail-rec" [ bench "tail-rec 0"      $ nf tailTestP (replicate 0 'a' ++ "b")
                             , bench "tail-rec 1"      $ nf tailTestP (replicate 1 'a' ++ "b")
                             , bench "tail-rec 10"     $ nf tailTestP (replicate 10 'a' ++ "b")
                             , bench "tail-rec 100"    $ nf tailTestP (replicate 100 'a' ++ "b")
                             , bench "tail-rec 1000"   $ nf tailTestP (replicate 1000 'a' ++ "b")
                             , bench "tail-rec 10,000" $ nf tailTestP (replicate 10000 'a' ++ "b")
                             ]
  
benchmark :: NFData a => String -> [FilePath] -> String -> (String -> Maybe a) -> Benchmark
benchmark name filenames lib parser = env (load filenames) (bgroup (concat [name, " (", lib, ")"]) . (tasks filenames))
  where
    load :: [FilePath] -> IO [String]
    load = traverse readFile
    tasks :: [FilePath] -> [String] -> [Benchmark]
    tasks filenames inputs = 
      let go [] _ = []
          go (f:fs) n = bench f (nf parser (inputs !! n)) : go fs (n+1)
      in go filenames 0

benchmarkT :: NFData a => String -> [FilePath] -> String -> (Text -> Maybe a) -> Benchmark
benchmarkT name filenames lib parser = env (load filenames) (bgroup (concat [name, " (", lib, ")"]) . (tasks filenames))
  where
    load :: [FilePath] -> IO [Text]
    load = traverse Data.Text.IO.readFile
    tasks :: [FilePath] -> [Text] -> [Benchmark]
    tasks filenames inputs = 
      let go [] _ = []
          go (f:fs) n = bench f (nf parser (inputs !! n)) : go fs (n+1)
      in go filenames 0

testP :: Text -> Maybe Char
testP = $$(Parsley.runParser Parsley.item)

main :: IO ()
--main = rnf (tailTestP (replicate 10000000 'a' ++ "b")) `seq` return ()
--main = print (testP (pack "abc"))
main = --{-
  let bfTest = benchmark "Brainfuck" ["inputs/helloworld.bf", "inputs/helloworld_golfed.bf", "inputs/compiler.bf"]
      bfTest' = benchmarkT "Brainfuck" ["inputs/helloworld.bf", "inputs/helloworld_golfed.bf", "inputs/compiler.bf"]
  in defaultMain [ bfTest "Parsley" brainfuckParsley
                 , bfTest' "Parsley" brainfuckParsley'
                 , bfTest "Parsley" (brainfuckParsley' . pack)
                 , bfTest "Parsec String" (parsecParseS ParsecParsers.brainfuck)
                 , bfTest "Parsec Text" (parsecParseT ParsecParsers.brainfuck)
                 , bfTest "Mega String" (megaParseS MegaparsecParsers.brainfuck)
                 , bfTest "Mega Text" (megaParseT MegaparsecParsers.brainfuck)
                 , bfTest "Native" NativeParsers.brainfuck
                 --, tailTest 
                 ]--}-}
