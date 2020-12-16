{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             DataKinds,
             TypeOperators,
             TypeFamilies,
             FlexibleContexts,
             NumericUnderscores,
             UnboxedTuples #-}
module Main where
import Criterion.Main         (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq        (NFData(rnf))
import GHC.Generics           (Generic)
import Control.Monad.Identity (Identity)
import Data.Text              (Text)
import Data.ByteString        (ByteString)
import Parsley                (Text16(..), CharList(..), Stream)
--import Parsley.Internal.Verbose ()
import qualified ParsleyParsers
import qualified ParsecParsers
import qualified MegaparsecParsers
import qualified AttoparsecParsers
import qualified NativeParsers
import qualified Happys.Brainfuck
import qualified Happys.Javascript
--import qualified Bisons.Bison as Bison
import qualified Parsley
import qualified Parsley.Combinator         as Parsley
import qualified Parsley.Fold               as Parsley
import qualified Text.Parsec                as Parsec
import qualified Text.Megaparsec            as Megaparsec
import qualified Data.Attoparsec.Text       as Attoparsec
import qualified Data.Text.IO
import qualified Data.ByteString
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Char8 (pack)
import CommonFunctions

brainfuckParsleyF :: FilePath -> IO (Maybe [BrainFuckOp])
brainfuckParsleyF = $$(Parsley.parseFromFile ParsleyParsers.brainfuck)

main :: IO ()
main = do
  --input <- readFile "inputs/big.js"
  --print (Happys.Javascript.runParser Happys.Javascript.javascript input)
  print (iterbenchP "abababababab")
  print (iterbenchP "abababababa")
  defaultMain [ predbench,iterbench
              , javascript
              , brainfuck
              --, nandlang
              ]

-- EOF
eofP :: String -> Maybe ()
eofP = $$(Parsley.runParser Parsley.eof)

eof :: Benchmark
eof = env (return ("", "a")) $ \(~(yay, nay)) -> bgroup "eof" [ bench "yay" $ nf eofP yay, bench "nay" $ nf eofP "nay"]

-- Pred bench
deriving instance Generic Pred
deriving instance NFData Pred

predbenchP :: String -> Maybe Pred
predbenchP = $$(Parsley.runParser ParsleyParsers.pred)

predbench :: Benchmark
predbench = env (return (concat ("f" : replicate 100_000 " && t"), take 500_000 (concat ("f" : replicate 100_000 " && t")))) $ \(~(good, bad)) ->
  bgroup "predbench" [ bench "good" $ nf predbenchP good
                     , bench "bad" $ nf predbenchP bad
                     ]

-- Iter bench (skipMany)
iterbenchP :: String -> Maybe ()
iterbenchP = $$(Parsley.runParser (Parsley.skipMany (Parsley.string "ab")))

iterbench :: Benchmark
iterbench = env (return (concat (replicate 100_000 "ab"), take 199_999 (concat (replicate 100_000 "ab")))) $ \(~(good, bad)) ->
  bgroup "iterbench" [ bench "good" $ nf iterbenchP good
                     , bench "bad" $ nf iterbenchP bad
                     ]

-- Regex Wars 2019
regexP :: ByteString -> Maybe Bool
regexP = $$(Parsley.runParser ParsleyParsers.regex)

regex :: Benchmark
regex = env (return ( Data.ByteString.Char8.pack (concat (replicate 1000 "ab"))
                    , Data.ByteString.Char8.pack (concat (replicate 10_000 "ab"))
                    , Data.ByteString.Char8.pack (concat (replicate 100_000 "ab")))) $ \(~(i1, i2, i3)) ->
  bgroup "regex" [ bench "regex 1000" $ nf regexP i1
                  , bench "regex 10000" $ nf regexP i2
                  , bench "regex 100000" $ nf regexP i3
                  ]

-- BrainFuck Benchmark
deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

brainfuckParsleyS :: String -> Maybe [BrainFuckOp]
brainfuckParsleyS = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyT :: Text16 -> Maybe [BrainFuckOp]
brainfuckParsleyT = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyB :: ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyB = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleySS :: CharList -> Maybe [BrainFuckOp]
brainfuckParsleySS = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyLB :: Data.ByteString.Lazy.ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyLB = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuck :: Benchmark
brainfuck =
  let bfTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe [BrainFuckOp]) -> Benchmark
      bfTest = benchmark ["benchmarks/inputs/helloworld.bf", "benchmarks/inputs/helloworld_golfed.bf", "benchmarks/inputs/compiler.bf"]
  in bgroup "Brainfuck"
       [ {-bfTest string          "Parsley (Stream)"          (brainfuckParsleySS . CharList)
       ,-} bfTest string          "Happy"                     Happys.Brainfuck.brainfuck
       , bfTest string          "Parsley (String)"          brainfuckParsleyS
       , bfTest text            "Parsley (Text)"            (brainfuckParsleyT . Text16)
       --, bfTest bytestring      "Parsley (ByteString)"      brainfuckParsleyB
       --, bfTest lazy_bytestring "Parsley (Lazy ByteString)" brainfuckParsleyLB
       , bfTest string          "Parsec (String)"           (parsecParse ParsecParsers.brainfuck)
       , bfTest text            "Parsec (Text)"             (parsecParse ParsecParsers.brainfuck)
       , bfTest string          "Mega (String)"             (megaParse MegaparsecParsers.brainfuck)
       , bfTest text            "Mega (Text)"               (megaParse MegaparsecParsers.brainfuck)
       --, bfTest bytestring      "Mega (Bytestring)"         (megaParse MegaparsecParsers.brainfuck)
       , bfTest text            "Atto (Text)"               (attoParse AttoparsecParsers.brainfuck)
       --, bfTest string          "Native"                    NativeParsers.brainfuck
       ]

-- Javascript
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

jsParsleyT :: Text -> Maybe JSProgram
jsParsleyT = $$(Parsley.runParser ParsleyParsers.javascript)

jsParsleyS :: String -> Maybe JSProgram
jsParsleyS = $$(Parsley.runParser ParsleyParsers.javascript)

javascript :: Benchmark
javascript =
  let jsTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe JSProgram) -> Benchmark
      jsTest = benchmark ["benchmarks/inputs/fibonacci.js", "benchmarks/inputs/heapsort.js", "benchmarks/inputs/game.js", "benchmarks/inputs/big.js"]
  in bgroup "Javascript"
       [ jsTest text   "Parsley (Text)"       jsParsleyT
       , jsTest string "Parsley (String)"     jsParsleyS
       , jsTest text   "Atto"                 (attoParse AttoparsecParsers.javascript)
       , jsTest string "Happy"                (Happys.Javascript.runParser Happys.Javascript.javascript)
       , jsTest string "Parsec (String)"      (parsecParse ParsecParsers.javascript)
       , jsTest text   "Parsec (Text)"        (parsecParse ParsecParsers.javascript)
       , jsTest string "Mega (String)"        (megaParse MegaparsecParsers.javascript)
       , jsTest text   "Mega (Text)"          (megaParse MegaparsecParsers.javascript)
       ]

-- Nandlang

{-nandParsleyB :: ByteString -> Maybe ()
nandParsleyB = $$(Parsley.runParser ParsleyParsers.nandlang)

nandlang :: Benchmark
nandlang =
  let nandTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe ()) -> Benchmark
      nandTest = benchmark ["benchmarks/inputs/fibonacci.nand", "benchmarks/inputs/fizzbuzz.nand", "benchmarks/inputs/arrays.nand"]
  in bgroup "Nandlang"
       [ nandTest bytestring "Parsley" nandParsleyB
       , nandTest bytestring "Bison"   Bison.nand ]
-}

-- Utils
parsecParse :: Parsec.Stream s Identity Char => ParsecParsers.Parser s a -> s -> Maybe a
parsecParse p = either (const Nothing) Just  . Parsec.parse p ""

megaParse :: (Megaparsec.Stream s, Megaparsec.Token s ~ Char) => MegaparsecParsers.Parser s a -> s -> Maybe a
megaParse = Megaparsec.parseMaybe

attoParse :: Attoparsec.Parser a -> Text -> Maybe a
attoParse p = Attoparsec.maybeResult . Attoparsec.parse p

string          :: FilePath -> IO String
string          = readFile
text            :: FilePath -> IO Text
text            = Data.Text.IO.readFile
bytestring      :: FilePath -> IO ByteString
bytestring      = Data.ByteString.readFile
lazy_bytestring :: FilePath -> IO Data.ByteString.Lazy.ByteString
lazy_bytestring = Data.ByteString.Lazy.readFile

benchmark :: (NFData a, NFData rep) => [FilePath] -> (FilePath -> IO rep) -> String -> (rep -> Maybe a) -> Benchmark
benchmark filenames load lib parser = env (traverse load filenames) (bgroup lib . (tasks filenames))
  where
    tasks filenames inputs = foldr (\f ts n -> bench f (nf parser (inputs !! n)) : ts (n+1)) (const []) filenames 0
