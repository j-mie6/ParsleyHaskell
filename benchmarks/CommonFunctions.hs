{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module CommonFunctions where

import Data.Int
import Data.Char (isAlpha, isSpace, isUpper, digitToInt, isDigit, isOctDigit, isHexDigit, isAlphaNum, ord, chr)
import Data.Maybe (fromMaybe)
import Text.Read (readMaybe)
import Data.Set (fromList, member)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Applicative

data Pred = And Pred Pred | Not Pred | T | F deriving Show
data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving Show

data Tape a = Tape [a] a [a]

evalBf :: [BrainFuckOp] -> IO ()
evalBf prog = go (Tape (repeat 0) 0 (repeat 0)) prog >> return ()
  where
    evalOp :: BrainFuckOp -> Tape Int32 -> IO (Tape Int32)
    evalOp RightPointer tape =                      return (right tape)
    evalOp LeftPointer  tape =                      return (left tape)
    evalOp Increment    tape = let x = read tape in return (write (succ x) tape)
    evalOp Decrement    tape = let x = read tape in return (write (pred x) tape)
    evalOp Output       tape = let x = read tape in do print (chr (fromEnum x)); return tape
    evalOp Input        tape =                      do x <- getChar; return (write (toEnum (ord x)) tape)
    evalOp (Loop p)     tape = let x = read tape in if x == 0 then return tape
                                                    else do tape' <- go tape p
                                                            if read tape' /= 0 then evalOp (Loop p) tape'
                                                            else return tape'

    go :: Tape Int32 -> [BrainFuckOp] -> IO (Tape Int32)
    go tape [] = return tape
    go tape (op:ops) = do tape' <- evalOp op tape; go tape' ops

    right :: Tape a -> Tape a
    right (Tape ls x (r:rs)) = Tape (x:ls) r rs
    left :: Tape a -> Tape a
    left (Tape (l:ls) x rs) = Tape ls l (x:rs)
    read :: Tape a -> a
    read (Tape _ x _) = x
    write :: a -> Tape a -> Tape a
    write x (Tape ls _ rs) = Tape ls x rs

{- JAVASCRIPT -}
type JSProgram = [JSElement]
type JSCompoundStm = [JSStm]
type JSExpr = [JSExpr']
data JSElement = JSFunction String [String] JSCompoundStm | JSStm JSStm deriving Show
data JSStm = JSSemi
           | JSIf JSExpr JSStm (Maybe JSStm)
           | JSWhile JSExpr JSStm
           | JSFor (Maybe (Either [JSVar] JSExpr)) (Maybe JSExpr) (Maybe JSExpr) JSStm
           | JSForIn (Either [JSVar] JSExpr) JSExpr JSStm
           | JSBreak
           | JSContinue
           | JSWith JSExpr JSStm
           | JSReturn (Maybe JSExpr)
           | JSBlock JSCompoundStm
           | JSNaked (Either [JSVar] JSExpr) deriving Show
data JSVar = JSVar String (Maybe JSExpr') deriving Show
data JSExpr' = JSAsgn   JSExpr' JSExpr'
             | JSCond   JSExpr' JSExpr' JSExpr'
             | JSOr     JSExpr' JSExpr'
             | JSAnd    JSExpr' JSExpr'
             | JSBitOr  JSExpr' JSExpr'
             | JSBitXor JSExpr' JSExpr'
             | JSBitAnd JSExpr' JSExpr'
             | JSEq     JSExpr' JSExpr'
             | JSNe     JSExpr' JSExpr'
             | JSLt     JSExpr' JSExpr'
             | JSGt     JSExpr' JSExpr'
             | JSLe     JSExpr' JSExpr'
             | JSGe     JSExpr' JSExpr'
             | JSShl    JSExpr' JSExpr'
             | JSShr    JSExpr' JSExpr'
             | JSAdd    JSExpr' JSExpr'
             | JSSub    JSExpr' JSExpr'
             | JSMul    JSExpr' JSExpr'
             | JSDiv    JSExpr' JSExpr'
             | JSMod    JSExpr' JSExpr'
             | JSUnary  JSUnary deriving Show
data JSUnary = JSPlus   JSUnary
             | JSNeg    JSUnary
             | JSBitNeg JSUnary
             | JSNot    JSUnary
             | JSInc    JSUnary
             | JSDec    JSUnary
             | JSNew    JSCons
             | JSDel    JSMember
             | JSMember JSMember
             | JSCons   JSCons deriving Show
jsPlus (JSUnary u)   = JSUnary (JSPlus u)
jsNeg (JSUnary u)    = JSUnary (JSNeg u)
jsBitNeg (JSUnary u) = JSUnary (JSBitNeg u)
jsNot (JSUnary u)    = JSUnary (JSNot u)
jsInc (JSUnary u)    = JSUnary (JSInc u)
jsDec (JSUnary u)    = JSUnary (JSDec u)
data JSMember = JSPrimExp JSAtom
              | JSAccess  JSAtom JSMember
              | JSIndex   JSAtom JSExpr
              | JSCall    JSAtom JSExpr deriving Show
data JSCons = JSQual String JSCons
            | JSConCall String JSExpr deriving Show
data JSAtom = JSParens JSExpr
            | JSArray  JSExpr
            | JSId     String
            | JSInt    Int
            | JSFloat  Double
            | JSString String
            | JSTrue
            | JSFalse
            | JSNull
            | JSThis deriving Show

jsCondExprBuild :: JSExpr' -> Maybe (JSExpr', JSExpr') -> JSExpr'
jsCondExprBuild c (Just (t, e)) = JSCond c t e
jsCondExprBuild c Nothing       = c

jsIdentStart :: Char -> Bool
jsIdentStart c = isAlpha c || c == '_'

jsIdentLetter :: Char -> Bool
jsIdentLetter c = isAlphaNum c || c == '_'

jsUnreservedName :: String -> Bool
jsUnreservedName = \s -> not (member s keys)
  where
    keys = fromList ["true", "false", "if", "else",
                     "for", "while", "break", "continue",
                     "function", "var", "new", "delete",
                     "this", "null", "return", "with"]

jsStringLetter :: Char -> Bool
jsStringLetter c = (c /= '"') && (c /= '\\') && (c > '\026')

nandIdentStart :: Char -> Bool
nandIdentStart c = isAlpha c || c == '_'

nandIdentLetter :: Char -> Bool
nandIdentLetter c = isAlphaNum c || c == '_'

nandUnreservedName :: String -> Bool
nandUnreservedName = \s -> not (member s keys)
  where
    keys = fromList ["if", "else", "while",
                     "function", "var"]

data JSToken = TokenNumber (Either Int Double)
             | TokenId String
             | TokenTrue
             | TokenFalse
             | TokenIf
             | TokenElse
             | TokenFor
             | TokenWhile
             | TokenWith
             | TokenBreak
             | TokenContinue
             | TokenFunction
             | TokenVar
             | TokenNew
             | TokenDelete
             | TokenThis
             | TokenNull
             | TokenReturn
             | TokenIn
             | TokenAss
             | TokenColon
             | TokenQuest
             | TokenDec
             | TokenInc
             | TokenAdd
             | TokenSub
             | TokenNot
             | TokenNeg
             | TokenMul
             | TokenDiv
             | TokenMod
             | TokenShl
             | TokenShr
             | TokenLeq
             | TokenLt
             | TokenGeq
             | TokenGt
             | TokenEq
             | TokenNeq
             | TokenBAnd
             | TokenBOr
             | TokenXor
             | TokenAnd
             | TokenOr
             | TokenString String
             | TokenLParen
             | TokenRParen
             | TokenLBracket
             | TokenRBracket
             | TokenLBrace
             | TokenRBrace
             | TokenDot
             | TokenSemi
             | TokenComma
             | Eof deriving (Eq, Show)

getId :: JSToken -> String
getId (TokenId x) = x

getNumber :: JSToken -> Either Int Double
getNumber (TokenNumber n) = n

getString :: JSToken -> String
getString (TokenString s) = s

isId :: JSToken -> Bool
isId (TokenId _) = True
isId _           = False

isNumber :: JSToken -> Bool
isNumber (TokenNumber _) = True
isNumber _               = False

isString :: JSToken -> Bool
isString (TokenString _) = True
isString _               = False

lexer :: forall m a. (MonadReader String m, Monad m, Alternative m) => (JSToken -> m a) -> m a
lexer k = do
  input <- ask
  case whiteSpace input of
    [] -> k Eof
    c:cs -> nextToken c cs (\t input -> local (const input) (k t))
  where
    nextToken :: forall a. Char -> String -> (JSToken -> String -> m a) -> m a
    nextToken ';' cs k = k TokenSemi cs
    nextToken ':' cs k = k TokenColon cs
    nextToken '.' cs k = k TokenDot cs
    nextToken ',' cs k = k TokenComma cs
    nextToken '?' cs k = k TokenQuest cs
    nextToken '(' cs k = k TokenLParen cs
    nextToken ')' cs k = k TokenRParen cs
    nextToken '[' cs k = k TokenLBracket cs
    nextToken ']' cs k = k TokenRBracket cs
    nextToken '{' cs k = k TokenLBrace cs
    nextToken '}' cs k = k TokenRBrace cs
    nextToken '*' cs k = k TokenMul cs
    nextToken '/' cs k = k TokenDiv cs
    nextToken '%' cs k = k TokenMod cs
    nextToken '~' cs k = k TokenNeg cs
    nextToken '!' ('=':cs) k = k TokenNeq cs
    nextToken '!' cs k = k TokenNot cs
    nextToken '=' ('=':cs) k = k TokenEq cs
    nextToken '=' cs k = k TokenAss cs
    nextToken '&' ('&':cs) k = k TokenAnd cs
    nextToken '&' cs k = k TokenBAnd cs
    nextToken '|' ('|':cs) k = k TokenOr cs
    nextToken '|' cs k = k TokenBOr cs
    nextToken '^' cs k = k TokenXor cs
    nextToken '<' ('<':cs) k = k TokenShl cs
    nextToken '<' ('=':cs) k = k TokenLeq cs
    nextToken '<' cs k = k TokenLt cs
    nextToken '>' ('>':cs) k = k TokenShr cs
    nextToken '>' ('=':cs) k = k TokenGeq cs
    nextToken '>' cs k = k TokenGt cs
    nextToken '-' ('-':cs) k = k TokenDec cs
    nextToken '-' cs k = k TokenSub cs
    nextToken '+' ('+':cs) k = k TokenInc cs
    nextToken '+' cs k = k TokenAdd cs
    nextToken '"' cs k = stringLit cs (k . TokenString)
    nextToken c cs k | isDigit c = numLit c cs (k . TokenNumber)
    nextToken 'b' ('r':'e':'a':'k':cs) k | noIdLetter cs = k TokenBreak cs
    nextToken 'c' ('o':'n':'t':'i':'n':'u':'e':cs) k | noIdLetter cs = k TokenContinue cs
    nextToken 'd' ('e':'l':'e':'t':'e':cs) k | noIdLetter cs = k TokenDelete cs
    nextToken 'e' ('l':'s':'e':cs) k | noIdLetter cs = k TokenElse cs
    nextToken 'f' ('a':'l':'s':'e':cs) k | noIdLetter cs = k TokenFalse cs
    nextToken 'f' ('o':'r':cs) k | noIdLetter cs = k TokenFor cs
    nextToken 'f' ('u':'n':'c':'t':'i':'o':'n':cs) k | noIdLetter cs = k TokenFunction cs
    nextToken 'i' ('f':cs) k | noIdLetter cs = k TokenIf cs
    nextToken 'i' ('n':cs) k | noIdLetter cs = k TokenIn cs
    nextToken 'n' ('e':'w':cs) k | noIdLetter cs = k TokenNew cs
    nextToken 'n' ('u':'l':'l':cs) k | noIdLetter cs = k TokenNull cs
    nextToken 'r' ('e':'t':'u':'r':'n':cs) k | noIdLetter cs = k TokenReturn cs
    nextToken 't' ('h':'i':'s':cs) k | noIdLetter cs = k TokenThis cs
    nextToken 't' ('r':'u':'e':cs) k | noIdLetter cs = k TokenTrue cs
    nextToken 'v' ('a':'r':cs) k | noIdLetter cs = k TokenVar cs
    nextToken 'w' ('h':'i':'l':'e':cs) k | noIdLetter cs = k TokenWhile cs
    nextToken 'w' ('i':'t':'h':cs) k | noIdLetter cs = k TokenWith cs
    nextToken c cs k | idLetter c = let (ident, rest) = span idLetter cs in k (TokenId (c:ident)) rest
    nextToken c cs k = empty

    idLetter :: Char -> Bool
    idLetter '_' = True
    idLetter c = isAlphaNum c

    noIdLetter :: String -> Bool
    noIdLetter (c:_) | idLetter c = False
    noIdLetter _ = True

    numLit :: forall a. Char -> String -> (Either Int Double -> String -> m a) -> m a
    numLit '0' = zeroNumFloat
    numLit d = (fromMaybe empty .) . decimalFloat . (d :)

    zeroNumFloat :: forall a. String -> (Either Int Double -> String -> m a) -> m a
    zeroNumFloat ('x':cs) k = hexadecimal cs (k . Left)
    zeroNumFloat ('X':cs) k = hexadecimal cs (k . Left)
    zeroNumFloat ('o':cs) k = octal cs (k . Left)
    zeroNumFloat ('O':cs) k = octal cs (k . Left)
    zeroNumFloat cs k = fromMaybe (k (Left 0) cs) (fractFloat 0 cs k <|> decimalFloat cs k)

    decimalFloat :: forall a. String -> (Either Int Double -> String -> m a) -> Maybe (m a)
    decimalFloat (d:cs) k | isDigit d = return (decimal (d:cs) (\x cs -> fromMaybe (k (Left x) cs) (fractFloat x cs k)))
    decimalFloat _ _ = empty

    fractFloat :: forall a. Int -> String -> (Either Int Double -> String -> m a) -> Maybe (m a)
    fractFloat x ('.':cs) = fractExpMaker ('.':) x cs
    fractFloat x ('e':cs) = exponent x cs
    fractFloat x ('E':cs) = exponent x cs
    fractFloat x cs = return Nothing

    exponent :: forall a. Int -> String -> (Either Int Double -> String -> m a) -> Maybe (m a)
    exponent x ('+':cs) = fractExpMaker ('e':) x cs
    exponent x ('-':cs) = fractExpMaker (('e':) . ('-':)) x cs
    exponent x cs = fractExpMaker ('e':) x cs

    fractExpMaker :: forall a. (String -> String) -> Int -> String -> (Either Int Double -> String -> m a) -> Maybe (m a)
    fractExpMaker conv x cs k = let (y, rest) = span isDigit cs in fmap (flip k rest . Right) (readMaybe (show x ++ conv y))

    number :: forall a. (Char -> Bool) -> (String -> String) -> String -> (Int -> String -> m a) -> m a
    number digit conv cs k = let (x, rest) = span digit cs in maybe empty (flip k rest) (readMaybe (conv x))
    decimal = number isDigit id
    hexadecimal = number isHexDigit ("0x" ++)
    octal = number isOctDigit ("0o" ++)

    stringLit :: forall a. String -> (String -> String -> m a) -> m a
    stringLit = go id
      where
        go :: forall a. (String -> String) -> String -> (String -> String -> m a) -> m a
        go acc ('\\':cs) k = escape cs (\c cs -> go (acc . (c:)) cs k)
        go acc ('"':cs) k = k (acc []) cs
        go acc (c:cs) k = go (acc . (c:)) cs k
        go acc _ k = empty

    escape :: forall a. String -> (Char -> String -> m a) -> m a
    escape ('a':cs) k = k '\a' cs
    escape ('b':cs) k = k '\b' cs
    escape ('f':cs) k = k '\f' cs
    escape ('n':cs) k = k '\n' cs
    escape ('t':cs) k = k '\t' cs
    escape ('v':cs) k = k '\v' cs
    escape ('\\':cs) k = k '\\' cs
    escape ('"':cs) k = k '"' cs
    escape ('\'':cs) k = k '\'' cs
    escape ('^':c:cs) k | isUpper c = k (toEnum (fromEnum c - fromEnum 'A' + 1)) cs
    escape ('A':'C':'K':cs) k = k '\ACK' cs
    escape ('B':'S':cs) k = k '\BS' cs
    escape ('B':'E':'L':cs) k = k '\BEL' cs
    escape ('C':'R':cs) k = k '\CR' cs
    escape ('C':'A':'N':cs) k = k '\CAN' cs
    escape ('D':'C':'1':cs) k = k '\DC1' cs
    escape ('D':'C':'2':cs) k = k '\DC2' cs
    escape ('D':'C':'3':cs) k = k '\DC3' cs
    escape ('D':'C':'4':cs) k = k '\DC4' cs
    escape ('D':'E':'L':cs) k = k '\DEL' cs
    escape ('D':'L':'E':cs) k = k '\DLE' cs
    escape ('E':'M':cs) k = k '\EM' cs
    escape ('E':'T':'X':cs) k = k '\ETX' cs
    escape ('E':'T':'B':cs) k = k '\ETB' cs
    escape ('E':'S':'C':cs) k = k '\ESC' cs
    escape ('E':'O':'T':cs) k = k '\EOT' cs
    escape ('E':'N':'Q':cs) k = k '\ENQ' cs
    escape ('F':'F':cs) k = k '\FF' cs
    escape ('F':'S':cs) k = k '\FS' cs
    escape ('G':'S':cs) k = k '\GS' cs
    escape ('H':'T':cs) k = k '\HT' cs
    escape ('L':'F':cs) k = k '\LF' cs
    escape ('N':'U':'L':cs) k = k '\NUL' cs
    escape ('N':'A':'K':cs) k = k '\NAK' cs
    escape ('R':'S':cs) k = k '\RS' cs
    escape ('S':'O':'H':cs) k = k '\SOH' cs
    escape ('S':'O':cs) k = k '\SO' cs
    escape ('S':'I':cs) k = k '\SI' cs
    escape ('S':'P':cs) k = k '\SP' cs
    escape ('S':'T':'X':cs) k = k '\STX' cs
    escape ('S':'Y':'N':cs) k = k '\SYN' cs
    escape ('S':'U':'B':cs) k = k '\SUB' cs
    escape ('U':'S':cs) k = k '\US' cs
    escape ('V':'T':cs) k = k '\VT' cs
    escape _ _ = empty

    whiteSpace :: String -> String
    whiteSpace (c:cs) | isSpace c = whiteSpace cs
    whiteSpace ('/':'*':cs) = multiLineComment cs
    whiteSpace ('/':'/':cs) = singleLineComment cs
    whiteSpace cs = cs
    singleLineComment :: String -> String
    singleLineComment = whiteSpace . dropWhile (/= '\n')
    multiLineComment :: String -> String
    multiLineComment ('*':'/':cs) = whiteSpace cs
    multiLineComment (_:cs) = multiLineComment cs
    multiLineComment [] = empty