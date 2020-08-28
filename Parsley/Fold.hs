{-# LANGUAGE PatternSynonyms #-}
module Parsley.Fold (
    module Parsley.Fold,
    module Primitives
  ) where

import Prelude hiding       (pure, (<*>), (<$>), (*>), (<*))
import Parsley.Alternative  ((<|>), option)
import Parsley.Applicative  (pure, (<*>), (<$>), (*>), (<*), (<:>), (<**>), void)
import Parsley.Core         (Parser, Defunc(FLIP, ID, COMPOSE, EMPTY, CONS, CONST, UNIT), ParserOps, pattern FLIP_H, pattern COMPOSE_H)
import Parsley.Register     (bind, get, modify, newRegister_)

import Parsley.Core.Primitives as Primitives (chainPre, chainPost)

{-chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre op p = newRegister_ ID $ \acc ->
  let go = modify acc (FLIP_H COMPOSE <$> op) *> go
       <|> get acc
  in go <*> p -}

{-chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost p op = newRegister p $ \acc ->
  let go = modify acc op *> go
       <|> get acc
  in go-}

-- Parser Folds
pfoldr :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser t a -> Parser t b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldr1 :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser t a -> Parser t b
pfoldr1 f k p = f <$> p <*> pfoldr f k p

pfoldl :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser t a -> Parser t b
pfoldl f k p = chainPost (pure k) ((FLIP <$> pure f) <*> p)

pfoldl1 :: (ParserOps repf, ParserOps repk) => repf (b -> a -> b) -> repk b -> Parser t a -> Parser t b
pfoldl1 f k p = chainPost (f <$> pure k <*> p) ((FLIP <$> pure f) <*> p)

-- Chain Combinators
chainl1' :: ParserOps rep => rep (a -> b) -> Parser t a -> Parser t (b -> a -> b) -> Parser t b
chainl1' f p op = chainPost (f <$> p) (FLIP <$> op <*> p)

chainl1 :: Parser t a -> Parser t (a -> a -> a) -> Parser t a
chainl1 = chainl1' ID

chainr1' :: ParserOps rep => rep (a -> b) -> Parser t a -> Parser t (a -> b -> b) -> Parser t b
chainr1' f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
           modify acc (FLIP_H COMPOSE <$> (op <*> x)) *> go
       <|> f <$> x
  in go <**> get acc

chainr1 :: Parser t a -> Parser t (a -> a -> a) -> Parser t a
chainr1 = chainr1' ID

chainr :: ParserOps rep => Parser t a -> Parser t (a -> a -> a) -> rep a -> Parser t a
chainr p op x = option x (chainr1 p op)

chainl :: ParserOps rep => Parser t a -> Parser t (a -> a -> a) -> rep a -> Parser t a
chainl p op x = option x (chainl1 p op)

-- Derived Combinators
many :: Parser t a -> Parser t [a]
many = pfoldr CONS EMPTY

manyN :: Int -> Parser t a -> Parser t [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser t a -> Parser t [a]
some = manyN 1

skipMany :: Parser t a -> Parser t ()
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . pfoldl CONST UNIT -- the void here will encourage the optimiser to recognise that the register is unused

skipManyN :: Int -> Parser t a -> Parser t ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: Parser t a -> Parser t ()
skipSome = skipManyN 1

sepBy :: Parser t a -> Parser t b -> Parser t [a]
sepBy p sep = option EMPTY (sepBy1 p sep)

sepBy1 :: Parser t a -> Parser t b -> Parser t [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: Parser t a -> Parser t b -> Parser t [a]
endBy p sep = many (p <* sep)

endBy1 :: Parser t a -> Parser t b -> Parser t [a]
endBy1 p sep = some (p <* sep)

sepEndBy :: Parser t a -> Parser t b -> Parser t [a]
sepEndBy p sep = option EMPTY (sepEndBy1 p sep)

{-sepEndBy1 :: Parser t a -> Parser t b -> Parser t [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1-}

sepEndBy1 :: Parser t a -> Parser t b -> Parser t [a]
sepEndBy1 p sep = newRegister_ ID $ \acc ->
  let go = modify acc (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p)
         *> (sep *> (go <|> get acc) <|> get acc)
  in go <*> pure EMPTY