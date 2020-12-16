{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module JavascriptBench.Happy.Parser where
import JavascriptBench.Shared
import Control.Monad.Reader
import Control.Applicative
import Data.Char (isSpace, isAlpha, isDigit, isAlphaNum, isUpper, isHexDigit, isOctDigit)
import Data.Maybe (fromMaybe)
import Data.List (span)
import Text.Read (readMaybe)
}

%name javascript Program
%lexer { lexer } { Eof }
%tokentype { Token }
%error { failParse }
%monad { Parser }

%token
    number { TokenNumber $$ }
    id { TokenId $$ }
    true { TokenTrue }
    false { TokenFalse }
    if { TokenIf }
    else  { TokenElse }
    for { TokenFor }
    while { TokenWhile }
    with { TokenWith }
    break  { TokenBreak }
    continue { TokenContinue }
    function { TokenFunction }
    var { TokenVar }
    new { TokenNew }
    delete { TokenDelete }
    this { TokenThis }
    null { TokenNull }
    return { TokenReturn }
    in { TokenIn }
    '=' { TokenAss }
    ':' { TokenColon }
    '?' { TokenQuest }
    '--' { TokenDec }
    '++' { TokenInc }
    '+' { TokenAdd }
    '-' { TokenSub }
    '!' { TokenNot }
    '~' { TokenNeg }
    '*' { TokenMul }
    '/' { TokenDiv }
    '%' { TokenMod }
    '<<' { TokenShl }
    '>>' { TokenShr }
    '<=' { TokenLeq }
    '<' { TokenLt }
    '>=' { TokenGeq }
    '>' { TokenGt }
    '==' { TokenEq }
    '!=' { TokenNeq }
    '&' { TokenBAnd }
    '|' { TokenBOr }
    '^' { TokenXor }
    '&&' { TokenAnd }
    '||' { TokenOr }
    string { TokenString $$ }
    '(' { TokenLParen }
    ')' { TokenRParen }
    '[' { TokenLBracket }
    ']' { TokenRBracket }
    '{' { TokenLBrace }
    '}' { TokenRBrace }
    '.' { TokenDot }
    ';' { TokenSemi }
    ',' { TokenComma }
%%

Program :: { JSProgram }
Program : Element Program { $1 : $2 }
        | { [] }

Element :: { JSElement }
Element : function id '(' Params ')' Compound { JSFunction $2 $4 $6 }
        | Stmt { JSStm $1 }

Params :: { [String] }
Params : id ',' Params { $1 : $3 }
       | id { [$1] }
       | { [] }

Compound :: { JSCompoundStm }
Compound : '{' Compound_ '}' { $2 }

Compound_ :: { [JSStm] }
Compound_ : Stmt Compound_ { $1 : $2 }
          | { [] }

Stmt :: { JSStm }
Stmt : ';' { JSSemi }
     | if '(' Expr ')' Stmt Else { JSIf $3 $5 $6 }
     | while '(' Expr ')' Stmt { JSWhile $3 $5 }
     | for '(' VarsOrExprs in Expr ')' Stmt { JSForIn $3 $5 $7 }
     | for '(' OptVarsOrExprs ';' OptExpr ';' OptExpr ')' Stmt { JSFor $3 $5 $7 $9}
     | break { JSBreak }
     | continue { JSContinue }
     | with '(' Expr ')' Stmt { JSWith $3 $5 }
     | return OptExpr { JSReturn $2 }
     | Compound { JSBlock $1 }
     | VarsOrExprs { JSNaked $1 }

Else :: { Maybe JSStm }
Else : else Stmt { Just $2 }
     | { Nothing }

OptExpr :: { Maybe JSExpr }
OptExpr : Expr { Just $1 }
        | { Nothing }

OptVarsOrExprs :: { Maybe (Either [JSVar] JSExpr) }
OptVarsOrExprs : VarsOrExprs { Just $1 }
               | { Nothing }

VarsOrExprs :: { Either [JSVar] JSExpr }
VarsOrExprs : var Vars { Left $2 }
            | Expr { Right $1 }

Vars :: { [JSVar] }
Vars : Variable ',' Vars { $1 : $3 }
     | Variable { [$1] }

Variable :: { JSVar }
Variable : id '=' Asgn { JSVar $1 (Just $3) }
         | id { JSVar $1 Nothing }

Expr :: { JSExpr }
Expr : Asgn ',' Expr { $1 : $3 }
     | Asgn { [$1] }

Asgn :: { JSExpr' }
Asgn : Asgn '=' CondExpr { JSAsgn $1 $3 }
     | CondExpr { $1 }

CondExpr :: { JSExpr' }
CondExpr : OrExpr Ternary { jsCondExprBuild $1 $2 }

Ternary :: { Maybe (JSExpr', JSExpr') }
Ternary : '?' Asgn ':' Asgn { Just ($2, $4) }
        | { Nothing }

-- Expressions
OrExpr :: { JSExpr' }
OrExpr : OrExpr '||' AndExpr { JSOr $1 $3 } | AndExpr { $1 }
AndExpr : AndExpr '&&' BitOrExpr { JSAnd $1 $3 } | BitOrExpr { $1 }
BitOrExpr : BitOrExpr '|' BitXorExpr { JSBitOr $1 $3 } | BitXorExpr { $1 }
BitXorExpr : BitXorExpr '^' BitAndExpr { JSBitXor $1 $3 } | BitAndExpr { $1 }
BitAndExpr : BitAndExpr '&' EqExpr { JSBitAnd $1 $3 } | EqExpr { $1 }
EqExpr : EqExpr '==' CompExpr { JSEq $1 $3 }
       | EqExpr '!=' CompExpr { JSNe $1 $3 }
       | CompExpr { $1 }
CompExpr : CompExpr '<=' ShiftExpr { JSLe $1 $3 }
         | CompExpr '<' ShiftExpr { JSLt $1 $3 }
         | CompExpr '>=' ShiftExpr { JSGe $1 $3 }
         | CompExpr '>' ShiftExpr { JSGt $1 $3 }
         | ShiftExpr { $1 }
ShiftExpr : ShiftExpr '<<' WeakArithExpr { JSShl $1 $3 }
          | ShiftExpr '>>' WeakArithExpr { JSShr $1 $3 }
          | WeakArithExpr { $1 }
WeakArithExpr : WeakArithExpr '+' StrongArithExpr { JSAdd $1 $3 }
              | WeakArithExpr '-' StrongArithExpr { JSSub $1 $3 }
              | StrongArithExpr { $1 }
StrongArithExpr : StrongArithExpr '*' Postfixes { JSMul $1 $3 }
                | StrongArithExpr '/' Postfixes { JSDiv $1 $3 }
                | StrongArithExpr '%' Postfixes { JSMod $1 $3 }
                | Postfixes { $1 }
Postfixes : Postfixes '--' { jsDec $1 }
          | Postfixes '++' { jsInc $1 }
          | Prefixes { $1 }
Prefixes : '--' Prefixes { jsDec $2 }
         | '++' Prefixes { jsInc $2 }
         | '-' Prefixes { jsNeg $2 }
         | '+' Prefixes { jsPlus $2 }
         | '~' Prefixes { jsBitNeg $2 }
         | '!' Prefixes { jsNot $2 }
         | MemOrCon { JSUnary $1 }

MemOrCon :: { JSUnary }
MemOrCon : delete Member { JSDel $2 }
         | new Con { JSCons $2 }
         | Member { JSMember $1 }

Con :: { JSCons }
Con : this '.' ConCall { JSQual "this" $3 }
    | ConCall { $1 }

ConCall :: { JSCons }
ConCall : id ConCall_ { $2 $1 }

ConCall_ :: { String -> JSCons }
ConCall_ : '.' ConCall { flip JSQual $2 }
         | '(' CommaAsgn ')' { flip JSConCall $2 }
         | { flip JSConCall [] }

CommaAsgn :: { [JSExpr'] }
CommaAsgn : Expr { $1 }
          | { [] }

Member :: { JSMember }
Member : PrimaryExpr Member_ { $2 $1 }

Member_ :: { JSAtom -> JSMember }
Member_ : '(' CommaAsgn ')' { flip JSCall $2 }
        | '[' Expr ']' { flip JSIndex $2 }
        | '.' Member { flip JSAccess $2 }
        | { JSPrimExp }

PrimaryExpr :: { JSAtom }
PrimaryExpr : '(' Expr ')' { JSParens $2 }
            | '[' CommaAsgn ']' { JSArray $2 }
            | id { JSId $1 }
            | number { either JSInt JSFloat $1 }
            | string { JSString $1 }
            | true { JSTrue }
            | false { JSFalse }
            | null { JSNull }
            | this { JSThis }

{
data Token = TokenNumber (Either Int Double)
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
           | Eof

newtype Parser a = Parser (ReaderT String Maybe a)
  deriving (Functor, Applicative, Alternative, Monad, MonadReader String)

failParse :: Token -> Parser a
failParse _ = Parser empty

runParser :: Parser a -> String -> Maybe a
runParser (Parser p) = runReaderT p

lexer :: (Token -> Parser a) -> Parser a
lexer k = do
  input <- ask
  case whiteSpace input of
    [] -> k Eof
    c:cs -> nextToken c cs (\t input -> local (const input) (k t))
  where
    nextToken :: Char -> String -> (Token -> String -> Parser a) -> Parser a
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

    numLit :: Char -> String -> (Either Int Double -> String -> Parser a) -> Parser a
    numLit '0' = zeroNumFloat
    numLit d = (fromMaybe empty .) . decimalFloat . (d :)

    zeroNumFloat :: String -> (Either Int Double -> String -> Parser a) -> Parser a
    zeroNumFloat ('x':cs) k = hexadecimal cs (k . Left)
    zeroNumFloat ('X':cs) k = hexadecimal cs (k . Left)
    zeroNumFloat ('o':cs) k = octal cs (k . Left)
    zeroNumFloat ('O':cs) k = octal cs (k . Left)
    zeroNumFloat cs k = fromMaybe (k (Left 0) cs) (fractFloat 0 cs k <|> decimalFloat cs k)

    decimalFloat :: String -> (Either Int Double -> String -> Parser a) -> Maybe (Parser a)
    decimalFloat (d:cs) k | isDigit d = return (decimal (d:cs) (\x cs -> fromMaybe (k (Left x) cs) (fractFloat x cs k)))
    decimalFloat _ _ = empty

    fractFloat :: Int -> String -> (Either Int Double -> String -> Parser a) -> Maybe (Parser a)
    fractFloat x ('.':cs) = fractExpMaker ('.':) x cs
    fractFloat x ('e':cs) = exponent x cs
    fractFloat x ('E':cs) = exponent x cs
    fractFloat x cs = return Nothing

    exponent :: Int -> String -> (Either Int Double -> String -> Parser a) -> Maybe (Parser a)
    exponent x ('+':cs) = fractExpMaker ('e':) x cs
    exponent x ('-':cs) = fractExpMaker (('e':) . ('-':)) x cs
    exponent x cs = fractExpMaker ('e':) x cs

    fractExpMaker :: (String -> String) -> Int -> String -> (Either Int Double -> String -> Parser a) -> Maybe (Parser a)
    fractExpMaker conv x cs k = let (y, rest) = span isDigit cs in fmap (flip k rest . Right) (readMaybe (show x ++ conv y))

    number :: (Char -> Bool) -> (String -> String) -> String -> (Int -> String -> Parser a) -> Parser a
    number digit conv cs k = let (x, rest) = span digit cs in maybe empty (flip k rest) (readMaybe (conv x))
    decimal = number isDigit id
    hexadecimal = number isHexDigit ("0x" ++)
    octal = number isOctDigit ("0o" ++)

    stringLit :: String -> (String -> String -> Parser a) -> Parser a
    stringLit = go id
      where
        go :: (String -> String) -> String -> (String -> String -> Parser a) -> Parser a
        go acc ('\\':cs) k = escape cs (\c cs -> go (acc . (c:)) cs k)
        go acc ('"':cs) k = k (acc []) cs
        go acc (c:cs) k = go (acc . (c:)) cs k
        go acc _ k = empty

    escape :: String -> (Char -> String -> Parser a) -> Parser a
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

}