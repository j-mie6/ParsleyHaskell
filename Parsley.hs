{-# LANGUAGE TemplateHaskell,
             DeriveLift,
             RankNTypes,
             TypeApplications,
             ScopedTypeVariables,
             FlexibleContexts,
             PatternSynonyms #-}
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
               , branch, select, match
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
               , Level(..), precedence
               -- Template Haskell Utils
               , code, (>*<), makeQ, _code, _val, WQ, Lift
               -- Template Haskell Crap
               , bool
               , module Input
               ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat, readFile)
import Input hiding               (PreparedInput(..))
import ParserAST                  (Parser, pure, (<*>), (*>), (<*), empty, (<|>), branch, match, satisfy, lookAhead, notFollowedBy, try, chainPre, chainPost, debug, _satisfy, _pure)
import Compiler                   (compile)
import Machine                    (exec, Ops)
import Utils                      (code, Quapplicative(..), WQ, Code)
import Data.Function              (fix)
import Data.List                  (foldl')
import Control.Monad.ST           (runST)
import Language.Haskell.TH.Syntax (Lift)
import Data.Text.IO               (readFile)
import Defunc                     (Defunc(CHAR, EQ_H, UNIT, APP, CONS, EMPTY, ID, FLIP, BLACK), pattern FLIP_H)

{-# INLINE fmap #-}
fmap :: WQ (a -> b) -> Parser a -> Parser b
fmap = _fmap . BLACK

{-# INLINE _fmap #-}
_fmap :: Defunc WQ (a -> b) -> Parser a -> Parser b
_fmap f = (_pure f <*>)

(<$>) :: WQ (a -> b) -> Parser a -> Parser b
(<$>) = fmap

void :: Parser a -> Parser ()
void p = p *> unit

(<$) :: WQ b -> Parser a -> Parser b
x <$ p = p *> pure x

($>) :: Parser a -> WQ b -> Parser b
($>) = flip (<$)

(<&>) :: Parser a -> WQ (a -> b) -> Parser b
(<&>) = flip fmap

{-# INLINE _liftA2 #-}
_liftA2 :: Defunc WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
_liftA2 f p q = _fmap f p <*> q

{-# INLINE liftA2 #-}
liftA2 :: WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 = _liftA2 . BLACK

liftA3 :: WQ (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

many :: Parser a -> Parser [a]
many = _pfoldr CONS EMPTY
{-many p = newRegister (pure (code id)) (\r ->
    let go = modify r (code flip >*< code (.) <$> (code (:) <$> p)) *> go
         <|> (makeQ ($ []) [||\f -> f []||] <$> get r)
    in go)-}

manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser a -> Parser [a]
some = manyN 1

skipMany :: Parser a -> Parser ()
--skipMany = pfoldr (code const >*< code id) (code ())
--skipMany = pfoldl (code const) (code ())
-- New implementation is stateless, so should work better!
skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp

skipManyN :: Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: Parser a -> Parser ()
skipSome = skipManyN 1

(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = code Left <$> p <|> code Right <$> q

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = sepBy1 p sep <|> _pure EMPTY

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

endBy1 :: Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end *> _pure EMPTY <|> p <:> go in go

someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

-- Additional Combinators
{-# INLINE (<:>) #-}
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = _liftA2 CONS

(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = _liftA2 (FLIP_H APP)

unit :: Parser ()
unit = _pure UNIT

(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (code (,))

(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)

  -- Auxillary functions
sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (_pure EMPTY)

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
char c = _satisfy (EQ_H (CHAR c)) *> _pure (CHAR c)

item :: Parser Char
item = satisfy (makeQ (const True) [|| const True ||])

-- Composite Combinators
optionally :: Parser a -> WQ b -> Parser b
optionally p x = p $> x <|> pure x

optional :: Parser a -> Parser ()
optional = flip optionally (code ())

option :: WQ a -> Parser a -> Parser a
option x p = p <|> pure x

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

bool :: a -> a -> Bool -> a
bool x y True  = x
bool x y False = y

constp :: Parser a -> Parser (b -> a)
constp = (code const <$>)

(<?|>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?|> (p, q) = branch (makeQ (bool (Left ()) (Right ())) [||bool (Left ()) (Right ())||] <$> cond) (constp p) (constp q)

(>?>) :: Parser a -> WQ (a -> Bool) -> Parser a
p >?> f = p >??> pure f

(>??>) :: Parser a -> Parser (a -> Bool) -> Parser a
px >??> pf = select (liftA2 (makeQ g qg) pf px) empty
  where
    g f x = if f x then Right x else Left ()
    qg = [||\f x -> if f x then Right x else Left ()||]

(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f empty

when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (_pure ID)

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (code Just <$> p)

-- Iterative Parsers
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = chainPost p (_fmap FLIP op <*> p)

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = let go = p <**> ((_fmap FLIP op <*> go) <|> _pure ID) in go

chainr :: Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainr p op x = chainr1 p op <|> pure x

chainl :: Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainl p op x = chainl1 p op <|> pure x

_pfoldr :: Defunc WQ (a -> b -> b) -> Defunc WQ b -> Parser a -> Parser b
_pfoldr f k p = chainPre (_fmap f p) (_pure k) 

pfoldr :: WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr f k = _pfoldr (BLACK f) (BLACK k)

pfoldl :: WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) (_fmap (FLIP_H (BLACK f)) p)

pfoldr1 :: WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr1 f k p = f <$> p <*> pfoldr f k p

pfoldl1 :: WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl1 f k p = chainPost (f <$> pure k <*> p) (_fmap (FLIP_H (BLACK f)) p)

data Level a = InfixL  [Parser (a -> a -> a)]
             | InfixR  [Parser (a -> a -> a)]
             | Prefix  [Parser (a -> a)]
             | Postfix [Parser (a -> a)]

precedence :: [Level a] -> Parser a -> Parser a
precedence levels atom = foldl' convert atom levels
  where
    convert x (InfixL ops)  = chainl1 x (choice ops)
    convert x (InfixR ops)  = chainr1 x (choice ops)
    convert x (Prefix ops)  = chainPre (choice ops) x
    convert x (Postfix ops) = chainPost x (choice ops)

runParser :: forall input a rep. (Input input rep, Ops rep) => Parser a -> Code (input -> Maybe a)
runParser p = [||\input -> runST $$(exec (prepare @input @rep [||input||]) (compile p))||]

parseFromFile :: Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]

-- Fixities
-- Functor
infixl 4 <$>
infixl 4 <$
infixl 4 $>
infixl 4 <&>
-- Applicative
--infixl 4 <*>
--infixl 4 <*
--infixl 4 *>
infixl 4 <**>
infixl 4 <:>
-- Monoidal
infixl 4 <~>
infixl 4 <~
infixl 4 ~>
-- Alternative
--infixl 3 <|>
infixl 3 <+>
-- Selective
infixl 4 >?>
infixl 4 <?|>
-- "Monadic"
infixl 1 ||=
infixl 1 >>
