{-# LANGUAGE TemplateHaskell,
             RankNTypes,
             FlexibleContexts,
             FlexibleInstances,
             MultiParamTypeClasses,
             AllowAmbiguousTypes,
             PatternSynonyms,
             GADTs #-}
module Parsley ( Parser, runParser, parseFromFile
               -- Functor
               , fmap, (<$>), (<$), ($>), (<&>), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2, liftA3
               -- Alternative
               , empty, (<|>), (<+>), optionally, optional, option, choice, oneOf, noneOf, maybeP
               -- Monoidal
               , unit, (<~>), (<~), (~>)
               -- Selective
               , branch, select, match, conditional, predicate
               -- "Monadic"
               , (||=), (>>)
               -- Primitives
               , satisfy, item
               , lookAhead, notFollowedBy, try
               -- Iteratives
               , chainl1, chainr1, chainPre, chainPost, chainl, chainr
               , pfoldr, pfoldl, pfoldr1, pfoldl1
               , many, manyN, some
               , skipMany, skipManyN, skipSome
               , sepBy, sepBy1, endBy, endBy1, manyTill, someTill
               -- Composites
               , char, eof, more
               , traverse, sequence, string, token, repeat
               , between
               , (<?|>), (>?>), (>??>), when, while, fromMaybeP
               , debug
               -- Expressions
               , Level(..), Prec(..), precedence, monolith, infixL, infixR, prefix, postfix
               -- Template Haskell Utils
               , code, (>*<), makeQ, _code, _val, WQ, Lift
               , module Parsley.Common.InputTypes
               , module Parsley.Frontend.Defunc
               ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat, readFile)
import Parsley.Frontend
import Parsley.Backend            (Input, prepare, Text16(..), CharList(..), eval)
import Parsley.Common.Utils       (code, Quapplicative(..), WQ, Code)
import Parsley.Common.InputTypes
import Data.Function              (fix)
import Language.Haskell.TH.Syntax (Lift)
import Data.Text.IO               (readFile)
import Parsley.Frontend.Defunc hiding (genDefunc, genDefunc1, genDefunc2)

class ParserOps rep where
  pure :: rep a -> Parser a
  satisfy :: rep (Char -> Bool) -> Parser Char
  conditional :: [(rep (a -> Bool), Parser b)] -> Parser a -> Parser b -> Parser b
  pfoldl :: ParserOps repk => rep (b -> a -> b) -> repk b -> Parser a -> Parser b
  pfoldl1 :: ParserOps repk => rep (b -> a -> b) -> repk b -> Parser a -> Parser b

instance ParserOps WQ where
  pure = pure . BLACK
  satisfy = satisfy . BLACK
  conditional cs p def = conditional (map (\(f, t) -> (BLACK f, t)) cs) p def
  pfoldl = pfoldl . BLACK
  pfoldl1 = pfoldl1 . BLACK

instance {-# INCOHERENT #-} x ~ Defunc => ParserOps x where
  pure = _pure
  satisfy = _satisfy
  conditional = _conditional
  pfoldl f k p = chainPost (pure k) (FLIP_H f <$> p)
  pfoldl1 f k p = chainPost (f <$> pure k <*> p) (FLIP_H f <$> p)

fmap :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

infixl 4 <$>
(<$>) :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
(<$>) = fmap

void :: Parser a -> Parser ()
void p = p *> unit

infixl 4 <$
(<$) :: ParserOps rep => rep b -> Parser a -> Parser b
x <$ p = p *> pure x

infixl 4 $>
($>) :: ParserOps rep => Parser a -> rep b -> Parser b
($>) = flip (<$)

infixl 4 <&>
(<&>) :: ParserOps rep => Parser a -> rep (a -> b) -> Parser b
(<&>) = flip fmap

liftA2 :: ParserOps rep => rep (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

liftA3 :: ParserOps rep => rep (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

many :: Parser a -> Parser [a]
many = pfoldr CONS EMPTY
{-many p = newRegister (pure ID) (\r ->
    let go = modify r (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p) *> go
         <|> (APP_H (FLIP_H APP) EMPTY <$> get r)
    in go)-}

manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser a -> Parser [a]
some = manyN 1

skipMany :: Parser a -> Parser ()
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . pfoldl (code const) UNIT -- the void here will encourage the optimiser to recognise that the register is unused

skipManyN :: Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: Parser a -> Parser ()
skipSome = skipManyN 1

infixl 3 <+>
(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = code Left <$> p <|> code Right <$> q

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = option EMPTY (sepBy1 p sep)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

endBy1 :: Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

sepEndBy :: Parser a -> Parser b -> Parser [a]
sepEndBy p sep = option EMPTY (sepEndBy1 p sep)

-- TODO Could do better with registers + difference list?
sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go

someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

-- Additional Combinators
{-# INLINE (<:>) #-}
infixl 4 <:>
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 CONS

infixl 4 <**>
(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (FLIP_H APP)

unit :: Parser ()
unit = pure UNIT

infixl 4 <~>
(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (code (,))

infixl 4 <~
(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

infixl 4 ~>
(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

infixl 1 >>
(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)

-- Auxillary functions
sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure EMPTY)

traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

string :: String -> Parser String
string = traverse char

oneOf :: [Char] -> Parser Char
oneOf cs = satisfy (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: [Char] -> Parser Char
noneOf cs = satisfy (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

token :: String -> Parser String
token = try . string

eof :: Parser ()
eof = notFollowedBy item

more :: Parser ()
more = lookAhead (void item)

repeat :: Int -> Parser a -> Parser [a]
repeat n p = traverse (const p) [1..n]

between :: Parser o -> Parser c -> Parser a -> Parser a
between open close p = open *> p <* close

-- Parsing Primitives
char :: Char -> Parser Char
char c = satisfy (EQ_H (CHAR c)) $> CHAR c

item :: Parser Char
item = satisfy (makeQ (const True) [|| const True ||])

-- Composite Combinators
optionally :: ParserOps rep => Parser a -> rep b -> Parser b
optionally p x = p $> x <|> pure x

optional :: Parser a -> Parser ()
optional = flip optionally UNIT

option :: ParserOps rep => rep a -> Parser a -> Parser a
option x p = p <|> pure x

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

constp :: Parser a -> Parser (b -> a)
constp = (code const <$>)

infixl 4 <?|>
(<?|>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?|> (p, q) = predicate ID cond p q

predicate :: ParserOps rep => rep (a -> Bool) -> Parser a -> Parser b -> Parser b -> Parser b
predicate cond p t e = conditional [(cond, t)] p e

filteredBy :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
filteredBy p f = p >??> pure f

infixl 4 >?>
(>?>) :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
(>?>) = filteredBy

infixl 4 >??>
(>??>) :: Parser a -> Parser (a -> Bool) -> Parser a
px >??> pf = select (liftA2 (makeQ g qg) pf px) empty
  where
    g f x = if f x then Right x else Left ()
    qg = [||\f x -> if f x then Right x else Left ()||]

match :: (Eq a, Lift a) => [a] -> Parser a -> (a -> Parser b) -> Parser b -> Parser b
match vs p f = _conditional (map (\v -> (EQ_H (code v), f v)) vs) p

infixl 1 ||=
(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f empty

when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure ID)

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (code Just <$> p)

-- Iterative Parsers
chainl1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
chainl1' f p op = chainPost (f <$> p) (FLIP <$> op <*> p)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = chainl1' ID

chainr1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
chainr1' f p op = let go = p <**> (option f (FLIP <$> op <*> go)) in go

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = chainr1' ID

chainr :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainr p op x = option x (chainr1 p op)

chainl :: ParserOps rep => Parser a -> Parser (a -> a -> a) -> rep a -> Parser a
chainl p op x = option x (chainl1 p op)

pfoldr :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldr1 :: (ParserOps repf, ParserOps repk) => repf (a -> b -> b) -> repk b -> Parser a -> Parser b
pfoldr1 f k p = f <$> p <*> pfoldr f k p

data Level a b = InfixL  [Parser (b -> a -> b)] (Defunc (a -> b))
               | InfixR  [Parser (a -> b -> b)] (Defunc (a -> b))
               | Prefix  [Parser (b -> b)]      (Defunc (a -> b))
               | Postfix [Parser (b -> b)]      (Defunc (a -> b))

class Monolith a b c where
  infixL  :: [Parser (b -> a -> b)] -> c
  infixR  :: [Parser (a -> b -> b)] -> c
  prefix  :: [Parser (b -> b)]      -> c
  postfix :: [Parser (b -> b)]      -> c

instance x ~ a => Monolith x a (Level a a) where
  infixL  = flip InfixL ID
  infixR  = flip InfixR ID
  prefix  = flip Prefix ID
  postfix = flip Postfix ID

instance {-# INCOHERENT #-} x ~ (WQ (a -> b) -> Level a b) => Monolith a b x where
  infixL  ops = InfixL ops . BLACK
  infixR  ops = InfixR ops . BLACK
  prefix  ops = Prefix ops . BLACK
  postfix ops = Postfix ops . BLACK

data Prec a b where
  NoLevel :: Prec a a
  Level :: Level a b -> Prec b c -> Prec a c

monolith :: [Level a a] -> Prec a a
monolith = foldr Level NoLevel

precedence :: Prec a b -> Parser a -> Parser b
precedence NoLevel atom = atom
precedence (Level lvl lvls) atom = precedence lvls (level lvl atom)
  where
    level (InfixL ops wrap) atom  = chainl1' wrap atom (choice ops)
    level (InfixR ops wrap) atom  = chainr1' wrap atom (choice ops)
    level (Prefix ops wrap) atom  = chainPre (choice ops) (wrap <$> atom)
    level (Postfix ops wrap) atom = chainPost (wrap <$> atom) (choice ops)

runParser :: Input input => Parser a -> Code (input -> Maybe a)
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p))||]

parseFromFile :: Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]
