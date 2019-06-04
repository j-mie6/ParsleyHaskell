{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveLift #-}
module Parsley ( Parser, runParser
               -- Functor
               , fmap, (<$>), (<$), ($>), (<&>), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2
               -- Alternative
               , empty, (<|>), optional, choice
               -- Monoidal
               , unit, (<~>), (<~), (~>)
               -- Selective
               , branch, select, match, (||=)
               -- Primitives
               , satisfy, item
               , lookAhead, notFollowedBy, try
               -- Iteratives
               , chainl1, chainr1, chainPre, chainPost
               , pfoldr, pfoldl, some, many, skipMany
               -- Composites
               , char, eof, more
               , traverse, sequence, string, token
               , (<?|>), (>?>), when, while, fromMaybeP
               -- Extras (TODO REMOVE TO TEST MODULE)
               , pred, isDigit, toDigit, digit, greaterThan5, plus, selectTest, Pred'
               ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import ParserAST                  (Parser, pure, (<*>), (*>), (<*), empty, (<|>), branch, match, satisfy, lookAhead, notFollowedBy, try, chainPre, chainPost)
import Compiler                   (compile)
import Machine                    (exec)
import Utils                      (lift', (>*<), WQ(..), TExpQ)
import Data.Function              (fix)
import Control.Monad.ST           (runST)
import Language.Haskell.TH.Syntax (Lift)

isDigit :: Char -> Bool
isDigit c
  |    c == '0' || c == '1' || c == '2' || c == '3'
    || c == '4' || c == '5' || c == '6' || c == '7'
    || c == '8' || c == '9' = True
  | otherwise = False

toDigit :: Char -> Int
toDigit c = fromEnum c - fromEnum '0'

digit :: Parser Int
digit = lift' toDigit <$> satisfy (lift' isDigit)

greaterThan5 :: Int -> Bool
greaterThan5 = (> 5)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> lift' (+)

selectTest :: Parser (Either Int String)
selectTest = pure (lift' (Left 10))

showi :: Int -> String
showi = show

data Pred' = And Pred' Pred' | Not Pred' | T | F deriving (Lift, Show)
pred :: Parser Pred'
pred = chainr1 term (lift' And <$ token "&&")
  where
    term :: Parser Pred'
    term = chainPre (lift' Not <$ token "!") atom
    atom :: Parser Pred'
    atom = (lift' T <$ token "t")
       <|> (lift' F <$ token "f")

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

some :: Parser a -> Parser [a]
some p = p <:> many p

skipMany :: Parser a -> Parser ()
skipMany = pfoldr (lift' const >*< lift' id) (lift' ())

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

  -- Auxillary functions
string :: String -> Parser String
string = foldr (<:>) (pure (lift' [])) . map char

token :: String -> Parser String
token = try . string

eof :: Parser ()
eof = notFollowedBy item

more :: Parser ()
more = lookAhead (void item)

-- Parsing Primitives
char :: Char -> Parser Char
char c = lift' c <$ satisfy (WQ (== c) [||(== c)||])

item :: Parser Char
item = satisfy (WQ (const True) [|| const True ||])

optional :: Parser a -> Parser ()
optional p = void p <|> unit

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

(||=) :: forall a b. (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f

when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure (lift' id))

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (WQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = chainPost p (lift' flip <$> op <*> p)

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = let go = p <**> ((lift' flip <$> op <*> go) <|> pure (lift' id)) in go

pfoldr :: WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldl :: WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) (lift' flip >*< f <$> p)

runParser :: Parser a -> TExpQ (String -> Maybe a)
runParser p = [||\input -> runST $$(exec [||input||] (compile p))||]

showM :: Parser a -> String
showM p = show (fst (compile p))