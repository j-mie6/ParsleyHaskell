{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where
import qualified Parsley
import qualified Text.Yoda as Yoda
import Criterion.Main (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq (NFData(rnf))
import Language.Haskell.TH.Syntax hiding (Match, match)
import LiftPlugin

manyTestParsley :: String -> Maybe ()
manyTestParsley = {-}$$(Parsley.runParser (Parsley.chainl1 Parsley.digit Parsley.plus))--}$$(Parsley.runParser (Parsley.skipMany (Parsley.debug "a" (Parsley.char 'a'))))

manyTestYodaBad :: Yoda.Parser Int
manyTestYodaBad = Yoda.chainl1 (Parsley.toDigit Yoda.<$> Yoda.satisfy (Parsley.isDigit)) ((+) Yoda.<$ Yoda.char '+')

manyTestYodaOk :: Yoda.Parser [Char]
manyTestYodaOk = Yoda.cull (Yoda.many (Yoda.char 'a'))

{-longChoice :: Parsley.Parser Char
longChoice = Parsley.choice (map Parsley.char (replicate 1000000 'a' ++ "b"))-}

combinatorGroup :: Benchmark
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
  ]

main :: IO ()
--main = rnf (Parsley.runParser longChoice "b") `seq` return ()
main = --rnf (Parsley.runParser (manyTestParsley) (replicate 1000000 'a')) `seq` return (){-
  defaultMain [
    combinatorGroup,
    crossMany
  ]--}
--main = print (manyTestParsley ("1+2+3+4+5"))
