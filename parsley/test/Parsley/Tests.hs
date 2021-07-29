module Main where
import Test.Tasty
import qualified Parsley.Alternative.Test as Alternative
import qualified Parsley.Applicative.Test as Applicative
import qualified Parsley.Combinator.Test as Combinator
import qualified Parsley.Fold.Test as Fold
import qualified Parsley.Precedence.Test as Precedence
import qualified Parsley.Primitive.Test as Primitive
import qualified Parsley.Register.Test as Register
import qualified Parsley.Selective.Test as Selective

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Parsley Tests" [ Primitive.tests
                                  , Alternative.tests
                                  , Applicative.tests
                                  , Combinator.tests
                                  , Fold.tests
                                  , Precedence.tests
                                  , Register.tests
                                  , Selective.tests
                                  ]