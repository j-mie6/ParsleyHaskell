{-# LANGUAGE TemplateHaskell,
             RankNTypes,
             FlexibleContexts,
             FlexibleInstances,
             MultiParamTypeClasses,
             AllowAmbiguousTypes,
             PatternSynonyms,
             GADTs #-}
module Parsley (
    module Parsley,
    module Core,
    module THUtils,
    Lift(..)
  ) where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), (>>), sequence, traverse, repeat, readFile)
import Data.Function              (fix)
import Data.Text.IO               (readFile)
import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Backend            (codeGen, Input, eval, prepare)
import Parsley.Core
import Parsley.Frontend           (compile)

import Parsley.Core as Core hiding     (_pure, _satisfy, _conditional)
import Parsley.Common.Utils as THUtils (code, Quapplicative(..), WQ, Code)

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

manyN :: Int -> Parser a -> Parser [a]
manyN n p = foldr (const (p <:>)) (many p) [1..n]

some :: Parser a -> Parser [a]
some = manyN 1

skipMany :: Parser a -> Parser ()
--skipMany p = let skipManyp = p *> skipManyp <|> unit in skipManyp
skipMany = void . pfoldl CONST UNIT -- the void here will encourage the optimiser to recognise that the register is unused

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

{-sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep =
  let seb1 = p <**> (sep *> (FLIP_H CONS <$> option EMPTY seb1)
                 <|> pure (APP_H (FLIP_H CONS) EMPTY))
  in seb1-}

sepEndBy1 :: Parser a -> Parser b -> Parser [a]
sepEndBy1 p sep = newRegister_ ID $ \acc ->
  let go = modify acc (COMPOSE_H (FLIP_H COMPOSE) CONS <$> p)
         *> optional (sep *> optional go)
  in go *> get acc <*> pure EMPTY

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
item = satisfy (APP_H CONST (code True))

{-notFollowedBy :: Parser a -> Parser ()
notFollowedBy p = newRegister_ (code True) $ \ok ->
     optional (try (lookAhead p *> put_ ok (code False)))
  *> get ok <?:> (unit, empty)-}

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

infixl 4 <?:>
(<?:>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?:> (p, q) = predicate ID cond p q

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
when p q = p <?:> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure ID)

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (code Just <$> p)

-- Stateful Parsers
newRegister_ :: ParserOps rep => rep a -> (forall r. Reg r a -> Parser b) -> Parser b
newRegister_ x = newRegister (pure x)

put_ :: ParserOps rep => Reg r a -> rep a -> Parser ()
put_ r = put r . pure

gets :: Reg r a -> Parser (a -> b) -> Parser b
gets r p = p <*> get r

gets_ :: ParserOps rep => Reg r a -> rep (a -> b) -> Parser b
gets_ r = gets r . pure

modify :: Reg r a -> Parser (a -> a) -> Parser ()
modify r p = put r (gets r p)

modify_ :: ParserOps rep => Reg r a -> rep (a -> a) -> Parser ()
modify_ r = modify r . pure

move :: Reg r1 a -> Reg r2 a -> Parser ()
move dst src = put dst (get src)

bind :: Parser a -> (Parser a -> Parser b) -> Parser b
bind p f = newRegister p (f . get)

local :: Reg r a -> Parser a -> Parser b -> Parser b
local r p q = bind (get r) $ \x -> put r p
                                *> q
                                <* put r x

swap :: Reg r1 a -> Reg r2 a -> Parser ()
swap r1 r2 = bind (get r1) $ \x -> move r1 r2
                                *> put r2 x

rollback :: Reg r a -> Parser b -> Parser b
rollback r p = bind (get r) $ \x -> p <|> put r x *> empty

for :: Parser a -> Parser (a -> Bool) -> Parser (a -> a) -> Parser () -> Parser ()
for init cond step body =
  newRegister init $ \i ->
    let cond' :: Parser Bool
        cond' = gets i cond
    in when cond' (while (body *> modify i step *> cond'))

-- Iterative Parsers
-- this form helps identify dead registers by optimisation in the backend, but might impact performance otherwise?
{-chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre op p = newRegister_ ID $ \acc ->
  let go = optional (modify acc (FLIP_H COMPOSE <$> op) *> go)
  in go *> get acc <*> p -}

-- this form helps identify dead registers by optimisation in the backend, but might impact performance otherwise?
{-chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost p op = newRegister p $ \acc ->
  let go = optional (modify acc op *> go)
  in go *> get acc-}

chainl1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (b -> a -> b) -> Parser b
chainl1' f p op = chainPost (f <$> p) (FLIP <$> op <*> p)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = chainl1' ID

-- this form helps identify dead registers by optimisation in the backend, but might impact performance otherwise?
chainr1' :: ParserOps rep => rep (a -> b) -> Parser a -> Parser (a -> b -> b) -> Parser b
chainr1' f p op = newRegister_ ID $ \acc ->
  let go = bind p $ \x ->
             modify acc (FLIP_H COMPOSE <$> (op <*> x)) *> go
         <|> (f <$> x)
  in go <**> get acc

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
runParser p = [||\input -> $$(eval (prepare [||input||]) (compile p codeGen))||]

parseFromFile :: Parser a -> Code (FilePath -> IO (Maybe a))
parseFromFile p = [||\filename -> do input <- readFile filename; return ($$(runParser p) (Text16 input))||]
