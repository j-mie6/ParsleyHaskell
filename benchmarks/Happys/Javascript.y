{
module Happys.Javascript where
import CommonFunctions
}

%name javascript Program
%tokentype { Token }
%error { const Nothing }
%monad { Maybe }

%token
    int { TokenInt $$ }
    id { TokenId $$ }
    true { TokenTrue }
    false { TokenFalse }
    if { TokenIf }
    else  { TokenElse }
    for { TokenFor }
    while { TokenWhile }
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
    char { TokenChar $$ }
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
Program : function id '(' Params ')' Compound Program { JSFunction $2 $4 $6 : $7  }
        | { [] }

Params :: { [String] }
Params : { [] }

Compound :: { JSCompoundStm }
Compound : { [] }

{
data Token = TokenInt Int
           | TokenId String
           | TokenTrue
           | TokenFalse
           | TokenIf
           | TokenElse
           | TokenFor
           | TokenWhile
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
           | TokenChar Char
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

lexer :: String -> [Token]
lexer = undefined
}