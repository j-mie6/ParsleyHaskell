module Main where
import qualified Parsley
import qualified Text.Yoda as Yoda
import Criterion.Main (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq (NFData(rnf))

manyTestParsley :: Parsley.Parser [Char]
manyTestParsley = Parsley.many (Parsley.char 'a')

manyTestYodaBad :: Yoda.Parser [Char]
manyTestYodaBad = Yoda.many (Yoda.char 'a')

manyTestYodaOk :: Yoda.Parser [Char]
manyTestYodaOk = Yoda.cull (Yoda.many (Yoda.char 'a'))

longChoice :: Parsley.Parser Char
longChoice = Parsley.choice (map Parsley.char (replicate 1000000 'a' ++ "b"))

combinatorGroup :: Benchmark
combinatorGroup =
  let longChoice' = Parsley.mkParser longChoice in
  bgroup "combinators" [
    --bench "longChoice"             $ nf (Parsley.runCompiledParser longChoice') "b",
    bench "manyTestParsley 0"      $ nf (Parsley.runParser manyTestParsley) (replicate 0 'a'),
    bench "manyTestParsley 1"      $ nf (Parsley.runParser manyTestParsley) (replicate 1 'a'),
    bench "manyTestParsley 10"     $ nf (Parsley.runParser manyTestParsley) (replicate 10 'a'),
    bench "manyTestParsley 100"    $ nf (Parsley.runParser manyTestParsley) (replicate 100 'a'),
    bench "manyTestParsley 1000"   $ nf (Parsley.runParser manyTestParsley) (replicate 1000 'a'),
    bench "manyTestParsley 10,000" $ nf (Parsley.runParser manyTestParsley) (replicate 10000 'a')
  ]

crossMany :: Benchmark
crossMany = env (return $ replicate 1000 'a') $ \input -> bgroup "many" [
    bench "manyParsley 1000" $ nf (Parsley.runParser manyTestParsley) input,
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
