{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module ParsleyParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import CommonFunctions
import Data.Char (isSpace, isUpper)
import Data.Maybe (catMaybes)

digit :: Parser Int
digit = code toDigit <$> satisfy (code isDigit)

greaterThan5 :: Int -> Bool
greaterThan5 = (> 5)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> code (+)

selectTest :: Parser (Either Int String)
selectTest = pure (code (Left 10))

showi :: Int -> String
showi = show

deriving instance Lift Pred

pred :: Parser Pred
pred = precedence [ Prefix [token "!" $> code Not]
                  , InfixR [token "&&" $> code And]] 
                  ( token "t" $> code T
                <|> token "f" $> code F)

phiTest :: Parser Char
--phiTest = try (char 'b') <|> char 'a' *> phiTest
phiTest = skipMany (char 'a') *> char 'b'

-- Brainfuck benchmark
deriving instance Lift BrainFuckOp

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

-- Regex Benchmark
regex :: Parser Bool
regex = skipMany (aStarb *> aStarb) *> char 'a' $> code True <|> pure (code False)
  where
    aStarb = aStar *> char 'b'
    aStar = skipMany (char 'a')

-- Javascript
deriving instance Lift JSElement
deriving instance Lift JSStm
deriving instance Lift JSVar
deriving instance Lift JSExpr'
deriving instance Lift JSUnary
deriving instance Lift JSMember
deriving instance Lift JSCons
deriving instance Lift JSAtom

javascript :: Parser JSProgram
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
    escapeCode = match escChrs (oneOf escChrs) escCode empty
      where
        escCode 'a' = pure (code ('\a'))
        escCode 'b' = pure (code ('\b'))
        escCode 'f' = pure (code ('\f'))
        escCode 'n' = pure (code ('\n'))
        escCode 't' = pure (code ('\t'))
        escCode 'v' = pure (code ('\v'))
        escCode '\\' = pure (code ('\\'))
        escCode '"' = pure (code ('"'))
        escCode '\'' = pure (code ('\''))
        escCode '^' = WQ (\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) [||\c -> toEnum (fromEnum c - fromEnum 'A' + 1)||] <$> satisfy (code isUpper)
        escCode 'A' = token "CK" $> code ('\ACK')
        escCode 'B' = token "S" $> code ('\BS') <|> token "EL" $> code ('\BEL')
        escCode 'C' = token "R" $> code ('\CR') <|> token "AN" $> code ('\CAN')
        escCode 'D' = token "C" *> (token "1" $> code ('\DC1')
                             <|> token "2" $> code ('\DC2')
                             <|> token "3" $> code ('\DC3')
                             <|> token "4" $> code ('\DC4'))
               <|> token "EL" $> code ('\DEL')
               <|> token "LE" $> code ('\DLE')
        escCode 'E' = token "M" $> code ('\EM')
               <|> token "T" *> (token "X" $> code ('\ETX')
                             <|> token "B" $> code ('\ETB'))
               <|> token "SC" $> code ('\ESC')
               <|> token "OT" $> code ('\EOT')
               <|> token "NQ" $> code ('\ENQ')
        escCode 'F' = token "F" $> code ('\FF') <|> token "S" $> code ('\FS')
        escCode 'G' = token "S" $> code ('\GS')
        escCode 'H' = token "T" $> code ('\HT')
        escCode 'L' = token "F" $> code ('\LF')
        escCode 'N' = token "UL" $> code ('\NUL') <|> token "AK" $> code ('\NAK')
        escCode 'R' = token "S" $> code ('\RS')
        escCode 'S' = token "O" *> option (code ('\SO')) (token "H" $> code ('\SOH'))
               <|> token "I" $> code ('\SI')
               <|> token "P" $> code ('\SP')
               <|> token "TX" $> code ('\STX')
               <|> token "YN" $> code ('\SYN')
               <|> token "UB" $> code ('\SUB')
        escCode 'U' = token "S" $> code ('\US')
        escCode 'V' = token "T" $> code ('\VT')
        -- TODO numeric
        escCode _ = empty--error "numeric escape codes not supported"