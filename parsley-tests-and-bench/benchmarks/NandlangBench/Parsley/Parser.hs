{-# OPTIONS_GHC -fplugin=Parsley.OverloadedQuotesPlugin #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module NandlangBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import Parsley.Combinator (token, oneOf, eof)
import Parsley.Fold (skipMany, skipSome)
--import Parsley.Garnish
import NandlangBench.Parsley.Functions
import Data.Char (isSpace)

nandlang :: Parser ()
nandlang = whitespace *> skipMany funcdef <* eof
  where
    index :: Parser ()
    index = brackets nat
    identifier :: Parser ()
    identifier = try (identStart *> skipMany identLetter) *> whitespace
    variable :: Parser ()
    variable = identifier *> optional index

    literal :: Parser ()
    literal = bit <|> charLit

    keyword :: String -> Parser ()
    keyword s = try (string s *> notIdentLetter) *> whitespace

    identStart = satisfy [|nandIdentStart|]
    identLetter = satisfy [|nandIdentLetter|]
    notIdentLetter = notFollowedBy identLetter

    bit :: Parser ()
    bit = (char '0' <|> char '1') *> whitespace

    nat :: Parser ()
    nat = decimal

    charLit :: Parser ()
    charLit = between (char '\'') (symbol '\'') charChar

    charChar :: Parser ()
    charChar = void (satisfy [|nandStringLetter|]) <|> esc

    esc :: Parser ()
    esc = char '\\' *> void (oneOf "0tnvfr")

    expr :: Parser ()
    expr = nandexpr *> skipMany (symbol '!' *> nandexpr)

    nandexpr :: Parser ()
    nandexpr = literal <|> funccallOrVar

    funccallOrVar :: Parser ()
    funccallOrVar = identifier *> optional (parens exprlist <|> index)

    exprlist = commaSep expr
    exprlist1 = commaSep1 expr
    varlist = commaSep variable
    varlist1 = commaSep1 variable

    funcparam = varlist *> optional (symbol ':' *> varlist)
    varstmt = optional (keyword "var") *> varlist1 *> symbol '=' *> exprlist1 <* semi
    ifstmt = keyword "if" *> expr *> block *> optional (keyword "else" *> block)
    whilestmt = keyword "while" *> expr *> block
    statement = ifstmt <|> whilestmt <|> try varstmt <|> expr <* semi
    block = braces (skipMany statement)
    funcdef = keyword "function" *> identifier *> parens funcparam *> block

    decimal :: Parser ()
    decimal = number (oneOf ['0'..'9'])
    hexadecimal = oneOf "xX" *> number (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number (oneOf ['0'..'7'])
    number :: Parser a -> Parser ()
    number digit = skipSome digit

    symbol :: Char -> Parser Char
    symbol c = char c <* whitespace
    parens :: Parser a -> Parser a
    parens = between (symbol '(') (symbol ')')
    brackets :: Parser a -> Parser a
    brackets = between (symbol '[') (symbol ']')
    braces :: Parser a -> Parser a
    braces = between (symbol '{') (symbol '}')
    semi :: Parser Char
    semi = symbol ';'
    comma :: Parser Char
    comma = symbol ','
    commaSep :: Parser a -> Parser ()
    commaSep p = optional (commaSep1 p)
    commaSep1 :: Parser a -> Parser ()
    commaSep1 p = p *> skipMany (comma *> p)

    space :: Parser ()
    space = void (satisfy [|isSpace|])
    whitespace :: Parser ()
    whitespace = skipMany (spaces <|> oneLineComment)
    spaces :: Parser ()
    spaces = skipSome space
    oneLineComment :: Parser ()
    oneLineComment = void (token "//" *> skipMany (satisfy [|(/= '\n')|]))