{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
module Regression.Issue27 where

import Prelude hiding (pure, (*>))

import Test.Tasty
import Test.Tasty.HUnit

import Parsley.Internal
import Parsley.Internal.Core.CombinatorAST (Parser(unParser), Combinator)
import Parsley.Internal.Common (Fix(In), Fix4(In4), cata, (\/))
import Parsley.Internal.Backend.CodeGenerator (codeGen)
import Parsley.Internal.Backend.Machine.LetBindings (Binding, body)
import Parsley.Internal.Backend.Machine.Types.Coins (willConsume)
import Parsley.Internal.Backend.Machine.Instructions
import Parsley.Internal.Frontend.Analysis.Cut (cutAnalysis)

import qualified Data.Set as Set (empty)

import Parsley.Internal.Verbose
--instance {-# INCOHERENT #-} Trace where trace = const id

-- Hand optimised version of string, so we don't have to run the frontend
string :: String -> Parser String
string str = foldr (\c p -> satisfy (EQ_H (LIFTED c)) *> p) (pure (LIFTED str)) str

-- No registers allowed!
toAST :: Parser a -> Fix Combinator a
toAST = cata (In \/ undefined) . unParser

codeGen' :: Fix Combinator a -> Binding o a a
codeGen' p = body (codeGen Nothing p Set.empty 0)

leadingCoinsUnderCatch :: Fix4 (Instr o) xs n r a -> Maybe Int
leadingCoinsUnderCatch (In4 (Catch (In4 (MetaInstr (AddCoins c) _)) _)) = Just (willConsume c)
leadingCoinsUnderCatch _ = Nothing

leadingCoins :: Fix4 (Instr o) xs n r a -> Maybe Int
leadingCoins (In4 (MetaInstr (AddCoins c) _)) = Just (willConsume c)
leadingCoins _ = Nothing

{- Example 1 -}
desc1 = "under outmost try max 1 coins should be factored without inner try"

ex1_p :: Fix Combinator String
ex1_p = toAST $ try $ string "123" <|> string "45"

test1 :: Assertion
test1 = let coins = leadingCoinsUnderCatch (codeGen' (cutAnalysis ex1_p))
        in (coins `elem` [Just 1, Nothing]) @? "expected 0 or 1 leading coins, got " ++ show coins

{- Example 2 -}
desc2 = "under outermost try 2 coins should be factored with inner try"

ex2_p :: Fix Combinator String
ex2_p = toAST $ try $ try (string "123") <|> string "45"

test2 :: Assertion
test2 = leadingCoins (codeGen' (cutAnalysis ex2_p)) @?= Just 2

{- Example 3 -}
desc3 = "max 1 coins should be factored without try"

ex3_p :: Fix Combinator String
ex3_p = toAST $ string "123" <|> string "45"

test3 :: Assertion
test3 = let coins = leadingCoins (codeGen' (cutAnalysis ex3_p))
        in (coins `elem` [Just 1, Nothing]) @? "expected 0 or 1 leading coins, got " ++ show coins

{- Example 4 -}
desc4 = "max 1 coins should be factored with no outer-most try"

ex4_p :: Fix Combinator String
ex4_p = toAST $ try (string "123") <|> try (string "45")

test4 :: Assertion
test4 = let coins = leadingCoins (codeGen' (cutAnalysis ex4_p))
        in (coins `elem` [Just 1, Nothing]) @? "expected 0 or 1 leading coins, got " ++ show coins

{- Example 5 -}
desc5 = ""

ex5_p :: Fix Combinator String
ex5_p = toAST $ (string "a" <|> pure (LIFTED "")) *> string "1234"

test5 :: Assertion
test5 = let coins = leadingCoinsUnderCatch (codeGen' (cutAnalysis ex5_p))
        in (coins `elem` [Just 1, Nothing]) @? "expected 0 or 1 leading coins, got " ++ show coins

{- Example 6 -}
desc6 = ""

ex6_p :: Fix Combinator String
ex6_p = toAST $ (string "abc" <|> string "def") *> string "123"

test6 :: Assertion
test6 = leadingCoinsUnderCatch (codeGen' (cutAnalysis ex6_p)) @?= Nothing

{- Example 7 -}
desc7 = ""

ex7_p :: Fix Combinator String
ex7_p = toAST $ (string "abc" <|> string "123") *> string "..." <|> string "def"

test7 :: Assertion
test7 = leadingCoinsUnderCatch (codeGen' (cutAnalysis ex7_p)) @?= Nothing

{- Example 8 -}
desc8 = ""

ex8_p :: Fix Combinator String
ex8_p = toAST $ (try (string "abc") <|> string "ade") *> string "..." <|> string "def"

test8 :: Assertion
test8 = leadingCoinsUnderCatch (codeGen' (cutAnalysis ex8_p)) @?= Nothing

tests :: TestTree
tests = testGroup "#27 Input checks in `Frontend` and `Backend` are not properly respecting cuts"
  [ testCase desc1 test1
  , testCase desc2 test2
  --, testCase desc3 test3
  --, testCase desc4 test4
  , testCase desc5 test5
  , testCase desc6 test6
  , testCase desc7 test7
  , testCase desc8 test8
  ]
