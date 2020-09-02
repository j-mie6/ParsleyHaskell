{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Happys.Javascript where
import CommonFunctions
import Control.Monad.Reader
import Control.Applicative
}

%name javascript Program
%lexer { lexer } { Eof }
%tokentype { JSToken }
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
newtype Parser a = Parser (ReaderT String Maybe a)
  deriving (Functor, Applicative, Alternative, Monad, MonadReader String)

failParse :: JSToken -> Parser a
failParse _ = Parser empty

runParser :: Parser a -> String -> Maybe a
runParser (Parser p) = runReaderT p
}