{-# LANGUAGE TemplateHaskell,
             DeriveLift,
             RankNTypes,
             TypeApplications,
             ScopedTypeVariables,
             FlexibleContexts #-}
module Parsley ( Parser, runParser, parseFromFile
               -- Functor
               , fmap, (<$>), (<$), ($>), (<&>), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2, liftA3
               -- Alternative
               , empty, (<|>), (<+>), optional, option, choice, oneOf, noneOf, maybeP, fromRightP
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
               , module Input
               ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat, readFile)
import Input hiding               (PreparedInput(..))
import ParserAST                  (Parser, pure, (<*>), (*>), (<*), empty, (<|>), branch, match, satisfy, lookAhead, notFollowedBy, try, chainPre, chainPost, debug)
import Compiler                   (compile)
import Machine                    (exec, Ops)
import Utils                      (lift', (>*<), WQ(..), TExpQ)
import Data.Function              (fix)
import Data.List                  (foldl')
import Control.Monad.ST           (runST)
import Language.Haskell.TH.Syntax (Lift)
import Data.Text.IO               (readFile)
import GHC.Stack                  (HasCallStack)

fmap :: HasCallStack => WQ (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

(<$>) :: HasCallStack => WQ (a -> b) -> Parser a -> Parser b
(<$>) = fmap

void :: HasCallStack => Parser a -> Parser ()
void p = p *> unit

(<$) :: HasCallStack => WQ b -> Parser a -> Parser b
x <$ p = p *> pure x

($>) :: HasCallStack => Parser a -> WQ b -> Parser b
($>) = flip (<$)

(<&>) :: HasCallStack => Parser a -> WQ (a -> b) -> Parser b
(<&>) = flip fmap

liftA2 :: HasCallStack => WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

liftA3 :: HasCallStack => WQ (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

many :: HasCallStack => Parser a -> Parser [a]
many = pfoldr (lift' (:)) (WQ [] [||[]||])

manyN :: HasCallStack => Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: HasCallStack => Parser a -> Parser [a]
some = manyN 1

skipMany :: HasCallStack => Parser a -> Parser ()
--skipMany = pfoldr (lift' const >*< lift' id) (lift' ())
--skipMany = pfoldl (lift' const) (lift' ())
-- New implementation is stateless, so should work better!
skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp

skipManyN :: HasCallStack => Int -> Parser a -> Parser ()
skipManyN n p = foldr (const (p *>)) (skipMany p) [1..n]

skipSome :: HasCallStack => Parser a -> Parser ()
skipSome = skipManyN 1

(<+>) :: HasCallStack => Parser a -> Parser b -> Parser (Either a b)
p <+> q = lift' Left <$> p <|> lift' Right <$> q

sepBy :: HasCallStack => Parser a -> Parser b -> Parser [a]
sepBy p sep = sepBy1 p sep <|> pure (WQ [] [||[]||])

sepBy1 :: HasCallStack => Parser a -> Parser b -> Parser [a]
sepBy1 p sep = p <:> many (sep *> p)

endBy :: HasCallStack => Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

endBy1 :: HasCallStack => Parser a -> Parser b -> Parser [a]
endBy1 p sep = some (p <* sep)

manyTill :: HasCallStack => Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> WQ [] [||[]||] <|> p <:> go in go

someTill :: HasCallStack => Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

-- Additional Combinators
(<:>) :: HasCallStack => Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (lift' (:))

(<**>) :: HasCallStack => Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (WQ (flip ($)) [|| (flip ($)) ||])

unit :: HasCallStack => Parser ()
unit = pure (lift' ())

(<~>) :: HasCallStack => Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (lift' (,))

(<~) :: HasCallStack => Parser a -> Parser b -> Parser a
(<~) = (<*)

(~>) :: HasCallStack => Parser a -> Parser b -> Parser b
(~>) = (*>)

(>>) :: HasCallStack => Parser a -> Parser b -> Parser b
(>>) = (*>)

  -- Auxillary functions
sequence :: HasCallStack => [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure (WQ [] [||[]||]))

traverse :: HasCallStack => (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

string :: HasCallStack => String -> Parser String
string = traverse char

oneOf :: HasCallStack => [Char] -> Parser Char
oneOf cs = satisfy (WQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: HasCallStack => [Char] -> Parser Char
noneOf cs = satisfy (WQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> TExpQ Char -> TExpQ Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

token :: HasCallStack => String -> Parser String
token = try . string

eof :: HasCallStack => Parser ()
eof = notFollowedBy item

more :: HasCallStack => Parser ()
more = lookAhead (void item)

repeat :: HasCallStack => Int -> Parser a -> Parser [a]
repeat n p = traverse (const p) [1..n]

between :: HasCallStack => Parser o -> Parser c -> Parser a -> Parser a
between open close p = open *> p <* close

-- Parsing Primitives
char :: HasCallStack => Char -> Parser Char
char c = lift' c <$ satisfy (WQ (== c) [||(== c)||])

item :: HasCallStack => Parser Char
item = satisfy (WQ (const True) [|| const True ||])

-- Composite Combinators
optional :: HasCallStack => Parser a -> Parser ()
optional p = void p <|> unit

option :: HasCallStack => WQ a -> Parser a -> Parser a
option x p = p <|> pure x

choice :: HasCallStack => [Parser a] -> Parser a
choice = foldr (<|>) empty

bool :: a -> a -> Bool -> a
bool x y True  = x
bool x y False = y

constp :: HasCallStack => Parser a -> Parser (b -> a)
constp = (lift' const <$>)

(<?|>) :: HasCallStack => Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?|> (p, q) = branch (WQ (bool (Left ()) (Right ())) [||bool (Left ()) (Right ())||] <$> cond) (constp p) (constp q)

partial :: (a -> Bool) -> (a -> b) -> a -> Maybe b
partial p f x = bool (Just (f x)) Nothing (p x)

(>?>) :: HasCallStack => Parser a -> WQ (a -> Bool) -> Parser a
--p >?> f = fromJustP ((lift' partial >*< f >*< lift' id) <$> p)
p >?> (WQ f qf) = fromRightP (WQ g qg <$> p)
  where
    g x = if f x then Right x else Left ()
    qg = [||\x -> if $$qf x then Right x else Left ()||]

(||=) :: (HasCallStack, Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f empty

when :: HasCallStack => Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: HasCallStack => Parser Bool -> Parser ()
while x = fix (when x)

select :: HasCallStack => Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure (lift' id))

fromMaybeP :: HasCallStack => Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (WQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: HasCallStack => Parser a -> Parser (Maybe a)
maybeP p = option (WQ Nothing [||Nothing||]) (lift' Just <$> p)

fromRightP :: HasCallStack => Parser (Either a b) -> Parser b
fromRightP p = select p empty

fromJustP :: HasCallStack => Parser (Maybe a) -> Parser a
fromJustP p = fromMaybeP p empty

chainl1 :: HasCallStack => Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = chainPost p (lift' flip <$> op <*> p)

chainr1 :: HasCallStack => Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = let go = p <**> ((lift' flip <$> op <*> go) <|> pure (lift' id)) in go

chainr :: HasCallStack => Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainr p op x = chainr1 p op <|> pure x

chainl :: HasCallStack => Parser a -> Parser (a -> a -> a) -> WQ a -> Parser a
chainl p op x = chainl1 p op <|> pure x

pfoldr :: HasCallStack => WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldl :: HasCallStack => WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) (lift' flip >*< f <$> p)

data Level a = InfixL  [Parser (a -> a -> a)]
             | InfixR  [Parser (a -> a -> a)]
             | Prefix  [Parser (a -> a)]
             | Postfix [Parser (a -> a)]

precedence :: HasCallStack => [Level a] -> Parser a -> Parser a
precedence levels atom = foldl' convert atom levels
  where
    convert x (InfixL ops)  = chainl1 x (choice ops)
    convert x (InfixR ops)  = chainr1 x (choice ops)
    convert x (Prefix ops)  = chainPre (choice ops) x
    convert x (Postfix ops) = chainPost x (choice ops)

runParser :: forall input a rep. (Input input rep, Ops rep) => Parser a -> TExpQ (input -> Maybe a)
runParser p = [||\input -> runST $$(exec (prepare @input @rep [||input||]) (compile p))||]

parseFromFile :: Parser a -> TExpQ (FilePath -> IO (Maybe a))
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
