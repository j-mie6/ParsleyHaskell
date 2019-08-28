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
import Data.List                  (intercalate)
import Data.Char                  (isAlphaNum)
import GHC.Stack

-- Parser wrapper type
newtype Parser a = Parser {unParser :: Free ParserF Void1 a}

-- Core smart constructors
pure :: HasCallStack => WQ a -> Parser a
pure = Parser . Op . Pure

(<*>) :: HasCallStack => Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (Op (p :<*>: q))

(<*) :: HasCallStack => Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (Op (p :<*: q))

(*>) :: HasCallStack => Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (Op (p :*>: q))

empty :: HasCallStack => Parser a
empty = Parser (Op Empty)

(<|>) :: HasCallStack => Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (Op (p :<|>: q))

satisfy :: HasCallStack => WQ (Char -> Bool) -> Parser Char
satisfy = Parser . Op . Satisfy

lookAhead :: HasCallStack => Parser a -> Parser a
lookAhead = Parser . Op . LookAhead . unParser

notFollowedBy :: HasCallStack => Parser a -> Parser ()
notFollowedBy = Parser . Op . NotFollowedBy . unParser

try :: HasCallStack => Parser a -> Parser a
try = Parser . Op . Try Nothing . unParser

match :: (HasCallStack, Eq a, Lift a) => [a] -> Parser a -> (a -> Parser b) -> Parser b -> Parser b
match vs (Parser p) f (Parser def) = Parser (Op (Match p (map (\v -> WQ (== v) [||(== v)||]) vs) (map (unParser . f) vs) def))

branch :: HasCallStack => Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (Op (Branch c p q))

chainPre :: HasCallStack => Parser (a -> a) -> Parser a -> Parser a
chainPre (Parser op) (Parser p) = Parser (Op (ChainPre op p))

chainPost :: HasCallStack => Parser a -> Parser (a -> a) -> Parser a
chainPost (Parser p) (Parser op) = Parser (Op (ChainPost p op))

debug :: HasCallStack => String -> Parser a -> Parser a
debug name (Parser p) = Parser (Op (Debug name p))

-- Fixities
-- Applicative
infixl 4 <*>
infixl 4 <*
infixl 4 *>
-- Alternative
infixl 3 <|>

-- Core datatype
-- http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Stack.html
-- Adding this allows us to track the origins of each AST node
data ParserF (k :: * -> *) (a :: *) where
    Pure          :: HasCallStack => WQ a -> ParserF k a
    Satisfy       :: HasCallStack => WQ (Char -> Bool) -> ParserF k Char
    (:<*>:)       :: HasCallStack => k (a -> b) -> k a -> ParserF k b
    (:*>:)        :: HasCallStack => k a -> k b -> ParserF k b
    (:<*:)        :: HasCallStack => k a -> k b -> ParserF k a
    (:<|>:)       :: HasCallStack => k a -> k a -> ParserF k a
    Empty         :: HasCallStack => ParserF k a
    Try           :: HasCallStack => Maybe Int -> k a -> ParserF k a
    LookAhead     :: HasCallStack => k a -> ParserF k a
    Let           :: HasCallStack => Bool -> MVar a -> k a -> ParserF k a
    NotFollowedBy :: HasCallStack => k a -> ParserF k ()
    Branch        :: HasCallStack => k (Either a b) -> k (a -> c) -> k (b -> c) -> ParserF k c
    Match         :: HasCallStack => k a -> [WQ (a -> Bool)] -> [k b] -> k b -> ParserF k b
    ChainPre      :: HasCallStack => k (a -> a) -> k a -> ParserF k a
    ChainPost     :: HasCallStack => k a -> k (a -> a) -> ParserF k a
    Debug         :: HasCallStack => String -> k a -> ParserF k a

callStackForParser :: ParserF f a -> CallStack
callStackForParser (Pure _)          = callStack
callStackForParser (Satisfy _)       = callStack
callStackForParser (_ :<*>: _)       = callStack
callStackForParser (_ :*>: _)        = callStack
callStackForParser (_ :<*: _)        = callStack
callStackForParser (_ :<|>: _)       = callStack
callStackForParser Empty             = callStack
callStackForParser (Try _ _)         = callStack
callStackForParser (LookAhead _)     = callStack
callStackForParser (Let _ _ _)       = callStack
callStackForParser (NotFollowedBy _) = callStack
callStackForParser (Branch _ _ _)    = callStack
callStackForParser (Match _ _ _ _)   = callStack
callStackForParser (ChainPre _ _)    = callStack
callStackForParser (ChainPost _ _)   = callStack
callStackForParser (Debug _ _)       = callStack

parserOrigin :: ParserF f a -> (String, SrcLoc)
parserOrigin = last . getCallStack . callStackForParser

prettyParserOrigin :: ParserF f a -> String
prettyParserOrigin p =
  let (name, loc) = parserOrigin p
  in if isAlphaNum (head name) then name ++ ", called at " ++ prettySrcLoc loc
     else
      let SrcLoc pkg mod file sl sc el ec = loc
          multi x y name
            | x == y  = concat [" ", name, " ", show x]
            | otherwise = concat [" ", name, "s " , show x, "-", show y]
      in concat [ "(", name, "), called at "
                , file, multi sl el "line"
                , " and"
                , multi sc ec "column"
                , " in ", pkg, ":", mod]

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
      alg (Match (Const1 p) fs qs (Const1 def))    = concat ["(match ", p, " [", intercalate ", " (map getConst1 qs), "] ", def, ")"]
      alg (ChainPre (Const1 op) (Const1 p))        = concat ["(chainPre ", op, " ", p, ")"]
      alg (ChainPost (Const1 p) (Const1 op))       = concat ["(chainPost ", p, " ", op, ")"]
      alg (Debug _ (Const1 p))                    = p