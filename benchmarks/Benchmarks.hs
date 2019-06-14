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

deriving instance Generic Pred
deriving instance NFData Pred
deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

parsecParse :: ParsecParsers.Parser a -> String -> Maybe a
parsecParse p input = either (const Nothing) Just (Parsec.parse p "" input)

manyTestParsley :: String -> Maybe Pred
manyTestParsley = -- $$(Parsley.runParser (Parsley.chainl1 Parsley.digit Parsley.plus))--}
                  -- $$(Parsley.runParser (Parsley.while ((Parsley.WQ (== 'a') [||(== 'a')||]) Parsley.<$> Parsley.item
                  --                        Parsley.<* Parsley.while ((Parsley.WQ (== 'b') [||(== 'b')||]) Parsley.<$> Parsley.item))))
                  $$(Parsley.runParser ({-Parsley.void -}ParsleyParsers.pred))

phiTestP :: String -> Maybe Char
phiTestP = $$(Parsley.runParser ParsleyParsers.phiTest)

--brainfuckParsley :: String -> Maybe [BrainFuckOp]
--brainfuckParsley = $$(Parsley.runParser ParsleyParsers.brainfuck)

{-longChoice :: Parsley.Parser Char
longChoice = Parsley.choice (map Parsley.char (replicate 1000000 'a' ++ "b"))-}

{-combinatorGroup :: Benchmark
combinatorGroup =
  --let longChoice' = Parsley.mkParser longChoice in
  bgroup "combinators" [
    --bench "longChoice"             $ nf (Parsley.runCompiledParser longChoice') "b",
    bench "manyTestParsley 0"      $ nf manyTestParsley (replicate 0 'a'),--(take 0 ('0':cycle "+1")),
    bench "manyTestParsley 1"      $ nf manyTestParsley (replicate 1 'a'),--(take 1 ('0':cycle "+1")),
    bench "manyTestParsley 10"     $ nf manyTestParsley (replicate 10 'a'),--(take 11 ('0':cycle "+1")),
    bench "manyTestParsley 100"    $ nf manyTestParsley (replicate 100 'a'),--(take 101 ('0':cycle "+1")),
    bench "manyTestParsley 1000"   $ nf manyTestParsley (replicate 1000 'a'),--(take 1001 ('0':cycle "+1")),
    bench "manyTestParsley 10,000" $ nf manyTestParsley (replicate 10000 'a')--(take 10001 ('0':cycle "+1"))
  ]

crossMany :: Benchmark
crossMany = env (return $ take 1001 ('0':cycle "+1")) $ \input -> bgroup "many" [
    bench "manyParsley 1000" $ nf manyTestParsley input,
    bench "manyYodaBad 1000" $ nf (Yoda.parse manyTestYodaBad)        input,
    bench "manyYodaOk 1000"  $ nf (Yoda.parse manyTestYodaOk)         input
  ]-}

main :: IO ()
--main = rnf (Parsley.runParser longChoice "b") `seq` return ()
{-main = --rnf (Parsley.runParser (manyTestParsley) (replicate 1000000 'a')) `seq` return (){-
  defaultMain [
    combinatorGroup,
    crossMany
  ]--}-}
main = print (manyTestParsley ("!!!!t&&!f&&t"))
