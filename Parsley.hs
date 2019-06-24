{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
module Parsley ( Parser, runParser
               -- Functor
               , fmap, (<$>), (<$), ($>), (<&>), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2
               -- Alternative
               , empty, (<|>), (<+>), optional, option, choice, oneOf, noneOf, maybeP
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
               , pfoldr, pfoldl
               , many, manyN, some
               , skipMany, skipManyN, skipSome
               , sepBy, sepBy1, endBy, endBy1, manyTill, someTill
               -- Composites
               , char, eof, more
               , traverse, sequence, string, token, repeat
               , between
               , (<?|>), (>?>), when, while, fromMaybeP
               , debug
               -- Expressions
               , Level(..), precedence
               -- Template Haskell Utils
               , lift', (>*<), WQ(..), Lift
               -- Template Haskell Crap
               , bool
               ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat)
import ParserAST                  (Parser, pure, (<*>), (*>), (<*), empty, (<|>), branch, match, satisfy, lookAhead, notFollowedBy, try, chainPre, chainPost, debug)
import Compiler                   (compile)
import Machine                    (exec)
import Utils                      (lift', (>*<), WQ(..), TExpQ)
import Data.Function              (fix)
import Data.List                  (foldl')
import Control.Monad.ST           (runST)
import Language.Haskell.TH.Syntax (Lift)

{-
PAPERS
1) PLDI - Similar to the Garnishing paper, talk about deep embeddings of parsers, type-safe representation,
          Free, type-safe compilation. Then go on to discuss the machine, its safety, its correspondance to
          DFA with state? Acknowledgement of staging here, but not dicussed in detail. Talk about how
          law based optimisations provide an additional boost. Mention a reliance on GHC to "do the right 
          thing". Optimisations are not guaranteed to terminate at this stage?
2) POPL - Foundational: differentiation of of grammars and how it corresponds to parsing. 
          Furthermore, show the correspondance with the abstract machines (left
          corresponds to handler stack pop, or backtracking)
3) PLDI - MicroCompiler architecture, a.k.a how to stop relying on GHC (1): relations to multi-stage programming
4) ICFP - Staging considerations for the machine (1): how is it actually orchestrated?
5) ?    - Abstract Interpretation (loop finding, termination analysis, constant input analysis, more more more)
6) IFL  - Error reporting in the parsers, lazy adaptation of the error stacks in P4S
7) ?    - Error correcting parsers using foundation layed in (2)
-}

fmap :: WQ (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

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

liftA2 :: WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

many :: Parser a -> Parser [a]
many p = pfoldr (lift' (:)) (WQ [] [||[]||]) p

manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser a -> Parser [a]
some = manyN 1

skipMany :: Parser a -> Parser ()
skipMany = pfoldr (lift' const >*< lift' id) (lift' ())
--skipMany = pfoldl (lift' const) (lift' ())
-- New implementation is stateless, so should work better!
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp

skipManyN :: Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: Parser a -> Parser ()
skipSome = skipManyN 1

(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = lift' Left <$> p <|> lift' Right <$> q

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = sepBy1 p sep <|> pure (WQ [] [||[]||])

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

endBy1 :: Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> WQ [] [||[]||] <|> p <:> go in go

someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

-- Additional Combinators
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (lift' (:))

(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (WQ (flip ($)) [|| (flip ($)) ||])

unit :: Parser ()
unit = pure (lift' ())

(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (lift' (,))

(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)

  -- Auxillary functions
sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure (WQ [] [||[]||]))

traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

string :: String -> Parser String
string = traverse char

oneOf :: [Char] -> Parser Char
oneOf = choice . map char--satisfy (WQ (flip elem cs) [||flip elem cs||])

noneOf :: [Char] -> Parser Char
noneOf cs = satisfy (WQ (not . flip elem cs) [||not . flip elem cs||])

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
char c = lift' c <$ satisfy (WQ (== c) [||(== c)||])

item :: Parser Char
item = satisfy (WQ (const True) [|| const True ||])

-- Composite Combinators
optional :: Parser a -> Parser ()
optional p = void p <|> unit

option :: WQ a -> Parser a -> Parser a
option x p = p <|> pure x

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

bool :: a -> a -> Bool -> a
bool x y True  = x
bool x y False = y

constp :: Parser a -> Parser (b -> a)
constp = (lift' const <$>)

(<?|>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?|> (p, q) = branch (WQ (bool (Left ()) (Right ())) [||bool (Left ()) (Right ())||] <$> cond) (constp p) (constp q)

(>?>) :: Parser a -> WQ (a -> Bool) -> Parser a
p >?> (WQ f qf) = select (WQ g qg <$> p) empty
  where
    g x = if f x then Right x else Left ()
    qg = [||\x -> if $$qf x then Right x else Left ()||]

(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f

when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure (lift' id))

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (WQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = lift' Just <$> p <|> pure (WQ Nothing [||Nothing||])

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = chainPost p (lift' flip <$> op <*> p)

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = let go = p <**> ((lift' flip <$> op <*> go) <|> pure (lift' id)) in go

chainr :: Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainr p op x = chainr1 p op <|> pure x

chainl :: Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainl p op x = chainl1 p op <|> pure x

pfoldr :: WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldl :: WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) (lift' flip >*< f <$> p)

data Level a = InfixL  [Parser (a -> a -> a)]
             | InfixR  [Parser (a -> a -> a)]
             | Prefix  [Parser (a -> a)]
             | Postfix [Parser (a -> a)]

-- TODO If subroutines are reintroduced to the language, then this needs subroutines to be efficient
precedence :: [Level a] -> Parser a -> Parser a
precedence levels atom = foldl' convert atom levels
  where
    convert x (InfixL ops)  = chainl1 x (choice ops)
    convert x (InfixR ops)  = chainr1 x (choice ops)
    convert x (Prefix ops)  = chainPre (choice ops) x
    convert x (Postfix ops) = chainPost x (choice ops)

runParser :: Parser a -> TExpQ (String -> Maybe a)
runParser p = [||\input -> runST $$(exec [||input||] (compile p))||]

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
