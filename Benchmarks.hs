module Main where
import qualified Parsley
import qualified Yoda
import Criterion.Main (Benchmark, bgroup, bench, whnf, nf, defaultMain)

manyTestParsley :: Parsley.Parser [Char]
manyTestParsley = Parsley.many (Parsley.char 'a')

manyTestYodaBad :: Yoda.Parser [Char]
manyTestYodaBad = Yoda.many (Yoda.char 'a')

manyTestYodaOk :: Yoda.Parser [Char]
manyTestYodaOk = Yoda.cull (Yoda.many (Yoda.char 'a'))

combinatorGroup :: Benchmark
combinatorGroup = bgroup "combinators" [
    bench "manyTestParsley 0"      $ nf (Parsley.runParser manyTestParsley) (replicate 0 'a'),
    bench "manyTestParsley 1"      $ nf (Parsley.runParser manyTestParsley) (replicate 1 'a'),
    bench "manyTestParsley 10"     $ nf (Parsley.runParser manyTestParsley) (replicate 10 'a'),
    bench "manyTestParsley 100"    $ nf (Parsley.runParser manyTestParsley) (replicate 100 'a'),
    bench "manyTestParsley 1000"   $ nf (Parsley.runParser manyTestParsley) (replicate 1000 'a'),
    bench "manyTestParsley 10,000" $ nf (Parsley.runParser manyTestParsley) (replicate 10000 'a')
  ]

crossMany :: Benchmark
crossMany = bgroup "many" [
    bench "manyParsley 1000" $ nf (Parsley.runParser manyTestParsley) (replicate 1000 'a'),
    bench "manyYodaBad 1000" $ nf (Yoda.parse manyTestYodaBad)        (replicate 1000 'a'),
    bench "manyYodaOk 1000"  $ nf (Yoda.parse manyTestYodaOk)         (replicate 1000 'a')
  ]

main :: IO ()
main = defaultMain [
    combinatorGroup,
    crossMany
  ]
