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
               , (<?|>), (>?>), (>??>), when, while, fromMaybeP
               , debug
               -- Registers
               , newRegister, get, put, modify, local, gets, swap, for, newRegister_, put_, modify_, gets_, Reg
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
import ParserAST                  (Parser, pure, (<*>), (*>), (<*), empty, (<|>), branch, match, satisfy, lookAhead, notFollowedBy, try, chainPre, chainPost, debug, newRegister, get, put, Reg)
import Compiler                   (compile)
import Machine                    (exec, Ops)
import Utils                      (lift', (>*<), WQ(..), TExpQ)
import Data.Function              (fix)
import Data.List                  (foldl')
import Control.Monad.ST           (runST)
import Language.Haskell.TH.Syntax (Lift)
import Data.Text.IO               (readFile)

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

liftA3 :: WQ (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

many :: Parser a -> Parser [a]
many = pfoldr (lift' (:)) (WQ [] [||[]||])
{-many p = newRegister (pure (lift' id)) (\r ->
    let go = modify r (lift' flip >*< lift' (.) <$> (lift' (:) <$> p)) *> go
         <|> (WQ ($ []) [||\f -> f []||] <$> get r)
    in go)-}

manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser a -> Parser [a]
some = manyN 1

skipMany :: Parser a -> Parser ()
--skipMany = pfoldr (lift' const >*< lift' id) (lift' ())
--skipMany = pfoldl (lift' const) (lift' ())
-- New implementation is stateless, so should work better!
skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp

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
oneOf cs = satisfy (WQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: [Char] -> Parser Char
noneOf cs = satisfy (WQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> TExpQ Char -> TExpQ Bool
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
p >?> f = p >??> pure f

(>??>) :: Parser a -> Parser (a -> Bool) -> Parser a
px >??> pf = select (liftA2 (WQ g qg) pf px) empty
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
select p q = branch p q (pure (lift' id))

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (WQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (WQ Nothing [||Nothing||]) (lift' Just <$> p)

-- Stateful Parsers
newRegister_ :: WQ a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister_ x gen = newRegister (pure x) gen

put_ :: Reg r a -> WQ a -> Parser ()
put_ r x = put r (pure x)

gets_ :: Reg r a -> WQ (a -> b) -> Parser b
gets_ r f = gets r (pure f)

gets :: Reg r a -> Parser (a -> b) -> Parser b
gets r p = get r <**> p -- Which way round should p evaluate?

modify_ :: Reg r a -> WQ (a -> a) -> Parser ()
modify_ r f = modify r (pure f)

modify :: Reg r a -> Parser (a -> a) -> Parser ()
modify r p = put r (get r <**> p) -- Which way round should p evaluate?

move :: Reg r1 a -> Reg r2 a -> Parser ()
move dst src = put dst (get src)

local :: Reg r a -> Parser a -> Parser b -> Parser b
local r p q = newRegister (get r) (\tmp -> put r p
                                        *> q
                                        <* move r tmp)

swap :: Reg r1 a -> Reg r2 a -> Parser ()
swap r1 r2 = newRegister (get r1) (\tmp -> move r1 r2
                                        *> move r2 tmp)

rollback :: Reg r a -> Parser b -> Parser b
rollback r p = newRegister (get r) (\save -> p <|> move r save *> empty)

for :: Parser a -> Parser (a -> Bool) -> Parser (a -> a) -> Parser () -> Parser ()
for init cond step body =
  newRegister init (\i ->
    let cond' :: Parser Bool
        cond' = gets i cond
    in when cond' (while (body *> modify i step *> cond')))

-- Iterative Parsers
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

precedence :: [Level a] -> Parser a -> Parser a
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
