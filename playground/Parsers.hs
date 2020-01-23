{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module Parsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred, repeat)
import Parsley
import Data.Char (isAlpha, isAlphaNum, isSpace, isUpper, isDigit, digitToInt)
import Data.Set (fromList, member)
import Data.Maybe (catMaybes)

data Expr = Var String | Num Int | Add Expr Expr deriving Show
data Asgn = Asgn String Expr deriving Show

data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving Show
deriving instance Lift BrainFuckOp

cinput :: Parser String
cinput = (char 'a' <|> char 'b') *> string "ab"

nfb :: Parser ()
nfb = notFollowedBy (char 'a') <|> void (string "ab")

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    {-bf = many ( lexeme ((token ">" $> code RightPointer)
                    <|> (token "<" $> code LeftPointer)
                    <|> (token "+" $> code Increment)
                    <|> (token "-" $> code Decrement)
                    <|> (token "." $> code Output)
                    <|> (token "," $> code Input)
                    <|> (between (lexeme (token "[")) (token "]") (code Loop <$> bf))))-}
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> code RightPointer
    op '<' = item $> code LeftPointer
    op '+' = item $> code Increment
    op '-' = item $> code Decrement
    op '.' = item $> code Output
    op ',' = item $> code Input
    op '[' = between (lexeme item) (try (char ']')) (code Loop <$> bf)

type JSProgram = [JSElement]
type JSCompoundStm = [JSStm]
type JSExpr = [JSExpr']
data JSElement = JSFunction String [String] JSCompoundStm | JSStm JSStm
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
           | JSNaked (Either [JSVar] JSExpr)
data JSVar = JSVar String (Maybe JSExpr')
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
             | JSUnary  JSUnary
data JSUnary = JSPlus   JSUnary
             | JSNeg    JSUnary
             | JSBitNeg JSUnary
             | JSNot    JSUnary
             | JSInc    JSUnary
             | JSDec    JSUnary
             | JSNew    JSCons
             | JSDel    JSMember
             | JSMember JSMember
             | JSCons   JSCons
jsPlus (JSUnary u)   = JSUnary (JSPlus u)
jsNeg (JSUnary u)    = JSUnary (JSNeg u)
jsBitNeg (JSUnary u) = JSUnary (JSBitNeg u)
jsNot (JSUnary u)    = JSUnary (JSNot u)
jsInc (JSUnary u)    = JSUnary (JSInc u)
jsDec (JSUnary u)    = JSUnary (JSDec u)
data JSMember = JSPrimExp JSAtom
              | JSAccess  JSAtom JSMember
              | JSIndex   JSAtom JSExpr
              | JSCall    JSAtom JSExpr
data JSCons = JSQual String JSCons
            | JSConCall String JSExpr
data JSAtom = JSParens JSExpr
            | JSArray  JSExpr
            | JSId     String
            | JSInt    Int
            | JSFloat  Double
            | JSString String
            | JSTrue
            | JSFalse
            | JSNull
            | JSThis

deriving instance Lift JSElement
deriving instance Lift JSStm
deriving instance Lift JSVar
deriving instance Lift JSExpr'
deriving instance Lift JSUnary
deriving instance Lift JSMember
deriving instance Lift JSCons
deriving instance Lift JSAtom

jsCondExprBuild :: JSExpr' -> Maybe (JSExpr', JSExpr') -> JSExpr'
jsCondExprBuild c (Just (t, e)) = JSCond c t e
jsCondexprBuild c Nothing       = c

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
                     "this", "null", "return"]

jsStringLetter :: Char -> Bool
jsStringLetter c = (c /= '"') && (c /= '\\') && (c > '\026')

{-failure :: Parser ()
failure = expr
  where
    expr :: Parser ()
    expr = item *> expr'
    expr' :: Parser ()
    expr' = expr *> expr'-}

failure :: Parser ()
failure = x
  where
    x = z <* y <* y
    y = try item
    z = x *> z


{-javascript :: Parser JSProgram
javascript = whitespace *> many element <* eof
  where
    element :: Parser JSElement
    element = keyword "function" *> liftA3 (code JSFunction) identifier (parens (commaSep identifier)) compound
          <|> code JSStm <$> stmt
    compound :: Parser JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser JSStm
    stmt = semi $> code JSSemi
       <|> keyword "if" *> liftA3 (code JSIf) parensExpr stmt (maybeP (keyword "else" *> stmt))
       <|> keyword "while" *> liftA2 (code JSWhile) parensExpr stmt
       <|> (keyword "for" *> parens
               (try (liftA2 (code JSForIn) varsOrExprs (keyword "in" *> expr))
            <|> liftA3 (code JSFor) (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> keyword "break" $> code JSBreak
       <|> keyword "continue" $> code JSContinue
       <|> keyword "with" *> liftA2 (code JSWith) parensExpr stmt
       <|> keyword "return" *> (code JSReturn <$> optExpr)
       <|> code JSBlock <$> compound
       <|> code JSNaked <$> varsOrExprs
    varsOrExprs :: Parser (Either [JSVar] JSExpr)
    varsOrExprs = keyword "var" *> commaSep1 variable <+> expr
    variable :: Parser JSVar
    variable = liftA2 (code JSVar) identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser JSExpr
    parensExpr = parens expr
    optExpr :: Parser (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser JSExpr
    expr = commaSep1 asgn
    asgn :: Parser JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> code JSAsgn)
    condExpr :: Parser JSExpr'
    condExpr = liftA2 (code jsCondExprBuild) expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser JSExpr'
    expr' = precedence
      [ Prefix  [ operator "--" $> code jsDec, operator "++" $> code jsInc
                , operator "-" $> code jsNeg, operator "+" $> code jsPlus
                , operator "~" $> code jsBitNeg, operator "!" $> code jsNot ]
      , Postfix [ operator "--" $> code jsDec, operator "++" $> code jsInc ]
      , InfixL  [ operator "*" $> code JSMul, operator "/" $> code JSDiv
                , operator "%" $> code JSMod ]
      , InfixL  [ operator "+" $> code JSAdd, operator "-" $> code JSSub ]
      , InfixL  [ operator "<<" $> code JSShl, operator ">>" $> code JSShr ]
      , InfixL  [ operator "<=" $> code JSLe, operator "<" $> code JSLt
                , operator ">=" $> code JSGe, operator ">" $> code JSGt ]
      , InfixL  [ operator "==" $> code JSEq, operator "!=" $> code JSNe ]
      , InfixL  [ try (operator "&") $> code JSBitAnd ]
      , InfixL  [ operator "^" $> code JSBitXor ]
      , InfixL  [ try (operator "|") $> code JSBitOr ]
      , InfixL  [ operator "&&" $> code JSAnd ]
      , InfixL  [ operator "||" $> code JSOr ]
      ]
      (code JSUnary <$> memOrCon)
    memOrCon :: Parser JSUnary
    memOrCon = keyword "delete" *> (code JSDel <$> member)
           <|> keyword "new" *> (code JSCons <$> con)
           <|> code JSMember <$> member
    con :: Parser JSCons
    con = liftA2 (code JSQual) (keyword "this" $> code "this") (dot *> conCall) <|> conCall
    conCall :: Parser JSCons
    conCall = identifier <**>
                (dot *> (code flip >*< code JSQual <$> conCall)
             <|> code flip >*< code JSConCall <$> parens (commaSep asgn)
             <|> pure (WQ (\name -> JSConCall name []) [||\name -> JSConCall name []||]))
    member :: Parser JSMember
    member = primaryExpr <**>
                (code flip >*< code JSCall <$> parens (commaSep asgn)
             <|> code flip >*< code JSIndex <$> brackets expr
             <|> dot *> (code flip >*< code JSAccess <$> member)
             <|> pure (code JSPrimExp))
    primaryExpr :: Parser JSAtom
    primaryExpr = code JSParens <$> parens expr
              <|> code JSArray <$> brackets (commaSep asgn)
              <|> code JSId <$> identifier
              <|> code either >*< code JSInt >*< code JSFloat <$> naturalOrFloat
              <|> code JSString <$> stringLiteral
              <|> code JSTrue <$ keyword "true"
              <|> code JSFalse <$ keyword "false"
              <|> code JSNull <$ keyword "null"
              <|> code JSThis <$ keyword "this"

    -- Token Parsers
    space :: Parser ()
    space = void (satisfy (code isSpace))
    whitespace :: Parser ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser String
    identifier = try ((identStart <:> many identLetter) >?> code jsUnreservedName) <* whitespace
    naturalOrFloat :: Parser (Either Int Double)
    naturalOrFloat = code Left <$> (code read <$> some (oneOf "0123456789"))
    stringLiteral :: Parser String
    stringLiteral = code catMaybes <$> between (token "\"") (token "\"") (many stringChar)
    symbol :: Char -> Parser Char
    symbol c = try (char c) <* whitespace
    parens :: Parser a -> Parser a
    parens = between (symbol '(') (symbol ')')
    brackets :: Parser a -> Parser a
    brackets = between (symbol '[') (symbol ']')
    braces :: Parser a -> Parser a
    braces = between (symbol '{') (symbol '}')
    dot :: Parser Char
    dot = symbol '.'
    semi :: Parser Char
    semi = symbol ';'
    comma :: Parser Char
    comma = symbol ','
    commaSep :: Parser a -> Parser [a]
    commaSep p = sepBy p comma
    commaSep1 :: Parser a -> Parser [a]
    commaSep1 p = sepBy1 p comma

    -- Let bindings
    spaces :: Parser ()
    spaces = skipSome space

    oneLineComment :: Parser ()
    oneLineComment = void (token "//" *> skipMany (satisfy (WQ (/= '\n') [||(/= '\n')||])))

    multiLineComment :: Parser ()
    multiLineComment =
      let inComment = void (token "*/")
                  <|> skipSome (noneOf "/*") *> inComment
                  <|> oneOf "/*" *> inComment
      in token "/*" *> inComment

    identStart = satisfy (code jsIdentStart)
    identLetter = satisfy (code jsIdentLetter)
    notIdentLetter = notFollowedBy identLetter
    notOpLetter = notFollowedBy (oneOf "+-*/=<>!~&|.%^")

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser (Maybe Char)
    stringChar = code Just <$> satisfy (code jsStringLetter) <|> stringEscape

    stringEscape :: Parser (Maybe Char)
    stringEscape = token "\\" *> (token "&" $> code Nothing
                              <|> spaces *> token "\\" $> code Nothing
                              <|> code Just <$> escapeCode)

    escapeCode :: Parser Char
    escapeCode = match escChrs (oneOf escChrs) code empty
      where
        code 'a' = pure (code ('\a'))
        code 'b' = pure (code ('\b'))
        code 'f' = pure (code ('\f'))
        code 'n' = pure (code ('\n'))
        code 't' = pure (code ('\t'))
        code 'v' = pure (code ('\v'))
        code '\\' = pure (code ('\\'))
        code '"' = pure (code ('"'))
        code '\'' = pure (code ('\''))
        code '^' = WQ (\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) [||\c -> toEnum (fromEnum c - fromEnum 'A' + 1)||] <$> satisfy (code isUpper)
        code 'A' = token "CK" $> code ('\ACK')
        code 'B' = token "S" $> code ('\BS') <|> token "EL" $> code ('\BEL')
        code 'C' = token "R" $> code ('\CR') <|> token "AN" $> code ('\CAN')
        code 'D' = token "C" *> (token "1" $> code ('\DC1')
                             <|> token "2" $> code ('\DC2')
                             <|> token "3" $> code ('\DC3')
                             <|> token "4" $> code ('\DC4'))
               <|> token "EL" $> code ('\DEL')
               <|> token "LE" $> code ('\DLE')
        code 'E' = token "M" $> code ('\EM')
               <|> token "T" *> (token "X" $> code ('\ETX')
                             <|> token "B" $> code ('\ETB'))
               <|> token "SC" $> code ('\ESC')
               <|> token "OT" $> code ('\EOT')
               <|> token "NQ" $> code ('\ENQ')
        code 'F' = token "F" $> code ('\FF') <|> token "S" $> code ('\FS')
        code 'G' = token "S" $> code ('\GS')
        code 'H' = token "T" $> code ('\HT')
        code 'L' = token "F" $> code ('\LF')
        code 'N' = token "UL" $> code ('\NUL') <|> token "AK" $> code ('\NAK')
        code 'R' = token "S" $> code ('\RS')
        code 'S' = token "O" *> option (code ('\SO')) (token "H" $> code ('\SOH'))
               <|> token "I" $> code ('\SI')
               <|> token "P" $> code ('\SP')
               <|> token "TX" $> code ('\STX')
               <|> token "YN" $> code ('\SYN')
               <|> token "UB" $> code ('\SUB')
        code 'U' = token "S" $> code ('\US')
        code 'V' = token "T" $> code ('\VT')
        -- TODO numeric
        code _ = empty--error "numeric escape codes not supported"-}