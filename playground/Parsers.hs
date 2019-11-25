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

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    {-bf = many ( lexeme ((token ">" $> lift' RightPointer)
                    <|> (token "<" $> lift' LeftPointer)
                    <|> (token "+" $> lift' Increment)
                    <|> (token "-" $> lift' Decrement)
                    <|> (token "." $> lift' Output)
                    <|> (token "," $> lift' Input)
                    <|> (between (lexeme (token "[")) (token "]") (lift' Loop <$> bf))))-}
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> lift' RightPointer
    op '<' = item $> lift' LeftPointer
    op '+' = item $> lift' Increment
    op '-' = item $> lift' Decrement
    op '.' = item $> lift' Output
    op ',' = item $> lift' Input
    op '[' = between (lexeme item) (try (char ']')) (lift' Loop <$> bf)

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
    element = keyword "function" *> liftA3 (lift' JSFunction) identifier (parens (commaSep identifier)) compound
          <|> lift' JSStm <$> stmt
    compound :: Parser JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser JSStm
    stmt = semi $> lift' JSSemi
       <|> keyword "if" *> liftA3 (lift' JSIf) parensExpr stmt (maybeP (keyword "else" *> stmt))
       <|> keyword "while" *> liftA2 (lift' JSWhile) parensExpr stmt
       <|> (keyword "for" *> parens
               (try (liftA2 (lift' JSForIn) varsOrExprs (keyword "in" *> expr))
            <|> liftA3 (lift' JSFor) (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> keyword "break" $> lift' JSBreak
       <|> keyword "continue" $> lift' JSContinue
       <|> keyword "with" *> liftA2 (lift' JSWith) parensExpr stmt
       <|> keyword "return" *> (lift' JSReturn <$> optExpr)
       <|> lift' JSBlock <$> compound
       <|> lift' JSNaked <$> varsOrExprs
    varsOrExprs :: Parser (Either [JSVar] JSExpr)
    varsOrExprs = keyword "var" *> commaSep1 variable <+> expr
    variable :: Parser JSVar
    variable = liftA2 (lift' JSVar) identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser JSExpr
    parensExpr = parens expr
    optExpr :: Parser (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser JSExpr
    expr = commaSep1 asgn
    asgn :: Parser JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> lift' JSAsgn)
    condExpr :: Parser JSExpr'
    condExpr = liftA2 (lift' jsCondExprBuild) expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser JSExpr'
    expr' = precedence
      [ Prefix  [ operator "--" $> lift' jsDec, operator "++" $> lift' jsInc
                , operator "-" $> lift' jsNeg, operator "+" $> lift' jsPlus
                , operator "~" $> lift' jsBitNeg, operator "!" $> lift' jsNot ]
      , Postfix [ operator "--" $> lift' jsDec, operator "++" $> lift' jsInc ]
      , InfixL  [ operator "*" $> lift' JSMul, operator "/" $> lift' JSDiv
                , operator "%" $> lift' JSMod ]
      , InfixL  [ operator "+" $> lift' JSAdd, operator "-" $> lift' JSSub ]
      , InfixL  [ operator "<<" $> lift' JSShl, operator ">>" $> lift' JSShr ]
      , InfixL  [ operator "<=" $> lift' JSLe, operator "<" $> lift' JSLt
                , operator ">=" $> lift' JSGe, operator ">" $> lift' JSGt ]
      , InfixL  [ operator "==" $> lift' JSEq, operator "!=" $> lift' JSNe ]
      , InfixL  [ try (operator "&") $> lift' JSBitAnd ]
      , InfixL  [ operator "^" $> lift' JSBitXor ]
      , InfixL  [ try (operator "|") $> lift' JSBitOr ]
      , InfixL  [ operator "&&" $> lift' JSAnd ]
      , InfixL  [ operator "||" $> lift' JSOr ]
      ]
      (lift' JSUnary <$> memOrCon)
    memOrCon :: Parser JSUnary
    memOrCon = keyword "delete" *> (lift' JSDel <$> member)
           <|> keyword "new" *> (lift' JSCons <$> con)
           <|> lift' JSMember <$> member
    con :: Parser JSCons
    con = liftA2 (lift' JSQual) (keyword "this" $> lift' "this") (dot *> conCall) <|> conCall
    conCall :: Parser JSCons
    conCall = identifier <**>
                (dot *> (lift' flip >*< lift' JSQual <$> conCall)
             <|> lift' flip >*< lift' JSConCall <$> parens (commaSep asgn)
             <|> pure (WQ (\name -> JSConCall name []) [||\name -> JSConCall name []||]))
    member :: Parser JSMember
    member = primaryExpr <**>
                (lift' flip >*< lift' JSCall <$> parens (commaSep asgn)
             <|> lift' flip >*< lift' JSIndex <$> brackets expr
             <|> dot *> (lift' flip >*< lift' JSAccess <$> member)
             <|> pure (lift' JSPrimExp))
    primaryExpr :: Parser JSAtom
    primaryExpr = lift' JSParens <$> parens expr
              <|> lift' JSArray <$> brackets (commaSep asgn)
              <|> lift' JSId <$> identifier
              <|> lift' either >*< lift' JSInt >*< lift' JSFloat <$> naturalOrFloat
              <|> lift' JSString <$> stringLiteral
              <|> lift' JSTrue <$ keyword "true"
              <|> lift' JSFalse <$ keyword "false"
              <|> lift' JSNull <$ keyword "null"
              <|> lift' JSThis <$ keyword "this"

    -- Token Parsers
    space :: Parser ()
    space = void (satisfy (lift' isSpace))
    whitespace :: Parser ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser String
    identifier = try ((identStart <:> many identLetter) >?> lift' jsUnreservedName) <* whitespace
    naturalOrFloat :: Parser (Either Int Double)
    naturalOrFloat = lift' Left <$> (lift' read <$> some (oneOf "0123456789"))
    stringLiteral :: Parser String
    stringLiteral = lift' catMaybes <$> between (token "\"") (token "\"") (many stringChar)
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

    identStart = satisfy (lift' jsIdentStart)
    identLetter = satisfy (lift' jsIdentLetter)
    notIdentLetter = notFollowedBy identLetter
    notOpLetter = notFollowedBy (oneOf "+-*/=<>!~&|.%^")

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser (Maybe Char)
    stringChar = lift' Just <$> satisfy (lift' jsStringLetter) <|> stringEscape

    stringEscape :: Parser (Maybe Char)
    stringEscape = token "\\" *> (token "&" $> lift' Nothing
                              <|> spaces *> token "\\" $> lift' Nothing
                              <|> lift' Just <$> escapeCode)

    escapeCode :: Parser Char
    escapeCode = match escChrs (oneOf escChrs) code empty
      where
        code 'a' = pure (lift' ('\a'))
        code 'b' = pure (lift' ('\b'))
        code 'f' = pure (lift' ('\f'))
        code 'n' = pure (lift' ('\n'))
        code 't' = pure (lift' ('\t'))
        code 'v' = pure (lift' ('\v'))
        code '\\' = pure (lift' ('\\'))
        code '"' = pure (lift' ('"'))
        code '\'' = pure (lift' ('\''))
        code '^' = WQ (\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) [||\c -> toEnum (fromEnum c - fromEnum 'A' + 1)||] <$> satisfy (lift' isUpper)
        code 'A' = token "CK" $> lift' ('\ACK')
        code 'B' = token "S" $> lift' ('\BS') <|> token "EL" $> lift' ('\BEL')
        code 'C' = token "R" $> lift' ('\CR') <|> token "AN" $> lift' ('\CAN')
        code 'D' = token "C" *> (token "1" $> lift' ('\DC1')
                             <|> token "2" $> lift' ('\DC2')
                             <|> token "3" $> lift' ('\DC3')
                             <|> token "4" $> lift' ('\DC4'))
               <|> token "EL" $> lift' ('\DEL')
               <|> token "LE" $> lift' ('\DLE')
        code 'E' = token "M" $> lift' ('\EM')
               <|> token "T" *> (token "X" $> lift' ('\ETX')
                             <|> token "B" $> lift' ('\ETB'))
               <|> token "SC" $> lift' ('\ESC')
               <|> token "OT" $> lift' ('\EOT')
               <|> token "NQ" $> lift' ('\ENQ')
        code 'F' = token "F" $> lift' ('\FF') <|> token "S" $> lift' ('\FS')
        code 'G' = token "S" $> lift' ('\GS')
        code 'H' = token "T" $> lift' ('\HT')
        code 'L' = token "F" $> lift' ('\LF')
        code 'N' = token "UL" $> lift' ('\NUL') <|> token "AK" $> lift' ('\NAK')
        code 'R' = token "S" $> lift' ('\RS')
        code 'S' = token "O" *> option (lift' ('\SO')) (token "H" $> lift' ('\SOH'))
               <|> token "I" $> lift' ('\SI')
               <|> token "P" $> lift' ('\SP')
               <|> token "TX" $> lift' ('\STX')
               <|> token "YN" $> lift' ('\SYN')
               <|> token "UB" $> lift' ('\SUB')
        code 'U' = token "S" $> lift' ('\US')
        code 'V' = token "T" $> lift' ('\VT')
        -- TODO numeric
        code _ = empty--error "numeric escape codes not supported"-}