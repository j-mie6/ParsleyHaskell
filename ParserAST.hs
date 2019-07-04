{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module ParserAST where

import Indexed                    (IFunctor, Free(Op), Void1, Const1(..), imap, fold)
import Machine                    (IMVar, MVar(..))
import Utils                      (WQ(..))
import Language.Haskell.TH.Syntax (Lift)

-- Parser wrapper type
newtype Parser a = Parser {unParser :: Free ParserF Void1 a}

-- Core smart constructors
pure :: WQ a -> Parser a
pure = Parser . Op . Pure

(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (Op (p :<*>: q))

(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (Op (p :<*: q))

(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (Op (p :*>: q))

empty :: Parser a
empty = Parser (Op Empty)

(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (Op (p :<|>: q))

satisfy :: WQ (Char -> Bool) -> Parser Char
satisfy = Parser . Op . Satisfy

lookAhead :: Parser a -> Parser a
lookAhead = Parser . Op . LookAhead . unParser

notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . Op . NotFollowedBy . unParser

try :: Parser a -> Parser a
try = Parser . Op . Try Nothing . unParser

match :: (Eq a, Lift a) => [a] -> Parser a -> (a -> Parser b) -> Parser b -> Parser b
match vs (Parser p) f (Parser def) = Parser (Op (Match p (map (\v -> WQ (== v) [||(== v)||]) vs) (map (unParser . f) vs) def))

branch :: Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (Op (Branch c p q))

chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre (Parser op) (Parser p) = Parser (Op (ChainPre op p))

chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost (Parser p) (Parser op) = Parser (Op (ChainPost p op))

debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (Op (Debug name p))

-- Fixities
-- Applicative
infixl 4 <*>
infixl 4 <*
infixl 4 *>
-- Alternative
infixl 3 <|>

-- Core datatype
data ParserF (k :: * -> *) (a :: *) where
    Pure          :: WQ a -> ParserF k a
    Satisfy       :: WQ (Char -> Bool) -> ParserF k Char
    (:<*>:)       :: k (a -> b) -> k a -> ParserF k b
    (:*>:)        :: k a -> k b -> ParserF k b
    (:<*:)        :: k a -> k b -> ParserF k a
    (:<|>:)       :: k a -> k a -> ParserF k a
    Empty         :: ParserF k a
    Try           :: Maybe Int -> k a -> ParserF k a
    LookAhead     :: k a -> ParserF k a
    Let           :: Bool -> MVar a -> k a -> ParserF k a
    NotFollowedBy :: k a -> ParserF k ()
    Branch        :: k (Either a b) -> k (a -> c) -> k (b -> c) -> ParserF k c
    Match         :: k a -> [WQ (a -> Bool)] -> [k b] -> k b -> ParserF k b
    ChainPre      :: k (a -> a) -> k a -> ParserF k a
    ChainPost     :: k a -> k (a -> a) -> ParserF k a
    Debug         :: String -> k a -> ParserF k a

-- Instances
instance IFunctor ParserF where
  imap _ (Pure x)          = Pure x
  imap _ (Satisfy p)       = Satisfy p
  imap f (p :<*>: q)       = f p :<*>: f q
  imap f (p :*>: q)        = f p :*>: f q
  imap f (p :<*: q)        = f p :<*: f q
  imap f (p :<|>: q)       = f p :<|>: f q
  imap _ Empty             = Empty
  imap f (Try n p)         = Try n (f p)
  imap f (LookAhead p)     = LookAhead (f p)
  imap f (Let r v p)       = Let r v (f p)
  imap f (NotFollowedBy p) = NotFollowedBy (f p)
  imap f (Branch b p q)    = Branch (f b) (f p) (f q)
  imap f (Match p fs qs d) = Match (f p) fs (map f qs) (f d)
  imap f (ChainPre op p)   = ChainPre (f op) (f p)
  imap f (ChainPost p op)  = ChainPost (f p) (f op)
  imap f (Debug name p)    = Debug name (f p)

instance Show (Free ParserF f a) where
  show = getConst1 . fold (const (Const1 "")) (Const1 . alg)
    where
      alg (Pure x)                               = "(pure x)"
      alg (Satisfy _)                            = "(satisfy f)"
      alg (Const1 pf :<*>: Const1 px)              = concat ["(", pf, " <*> ",  px, ")"]
      alg (Const1 p :*>: Const1 q)                 = concat ["(", p, " *> ", q, ")"]
      alg (Const1 p :<*: Const1 q)                 = concat ["(", p, " <* ", q, ")"]
      alg (Const1 p :<|>: Const1 q)                = concat ["(", p, " <|> ", q, ")"]
      alg Empty                                  = "empty"
      alg (Try Nothing (Const1 p))                = concat ["(try ? ", p, ")"]
      alg (Try (Just n) (Const1 p))               = concat ["(try ", show n, " ", p, ")"]
      alg (LookAhead (Const1 p))                  = concat ["(lookAhead ", p, ")"]
      alg (Let False v _)                        = concat ["(let-bound ", show v, ")"]
      alg (Let True v _)                         = concat ["(rec ", show v, ")"]
      alg (NotFollowedBy (Const1 p))              = concat ["(notFollowedBy ", p, ")"]
      alg (Branch (Const1 b) (Const1 p) (Const1 q)) = concat ["(branch ", b, " ", p, " ", q, ")"]
      alg (Match (Const1 p) fs qs (Const1 def))    = concat ["(match ", p, " ", show (map getConst1 qs), " ", def, ")"]
      alg (ChainPre (Const1 op) (Const1 p))        = concat ["(chainPre ", op, " ", p, ")"]
      alg (ChainPost (Const1 p) (Const1 op))       = concat ["(chainPost ", p, " ", op, ")"]
      alg (Debug _ (Const1 p))                    = p