module JavascriptBench.Attoparsec.Parser where

import Shared.Attoparsec.Extended
import JavascriptBench.Shared

import Data.Char (isSpace, isUpper, digitToInt)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)

javascript :: Parser JSProgram
javascript = whitespace *> many element <* endOfInput
  where
    element :: Parser JSElement
    element = keyword "function" *> liftA3 JSFunction identifier (parens (commaSep identifier)) compound
          <|> JSStm <$> stmt
    compound :: Parser JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser JSStm
    stmt = semi $> JSSemi
       <|> keyword "if" *> liftA3 JSIf parensExpr stmt (maybeP (keyword "else" *> stmt))
       <|> keyword "while" *> liftA2 JSWhile parensExpr stmt
       <|> (keyword "for" *> parens
               (try (liftA2 JSForIn varsOrExprs (keyword "in" *> expr))
            <|> liftA3 JSFor (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> keyword "break" $> JSBreak
       <|> keyword "continue" $> JSContinue
       <|> keyword "with" *> liftA2 JSWith parensExpr stmt
       <|> keyword "return" *> (JSReturn <$> optExpr)
       <|> JSBlock <$> compound
       <|> JSNaked <$> varsOrExprs
    varsOrExprs :: Parser (Either [JSVar] JSExpr)
    varsOrExprs = (keyword "var" *> commaSep1 variable) <+> expr
    variable :: Parser JSVar
    variable = liftA2 JSVar identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser JSExpr
    parensExpr = parens expr
    optExpr :: Parser (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser JSExpr
    expr = commaSep1 asgn
    asgn :: Parser JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> JSAsgn)
    condExpr :: Parser JSExpr'
    condExpr = liftA2 jsCondExprBuild expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser JSExpr'
    expr' = precedence
      [ Prefix  [ operator "--" $> jsDec, operator "++" $> jsInc
                , operator "-" $> jsNeg, operator "+" $> jsPlus
                , operator "~" $> jsBitNeg, operator "!" $> jsNot ]
      , Postfix [ operator "--" $> jsDec, operator "++" $> jsInc ]
      , InfixL  [ operator "*" $> JSMul, operator "/" $> JSDiv
                , operator "%" $> JSMod ]
      , InfixL  [ operator "+" $> JSAdd, operator "-" $> JSSub ]
      , InfixL  [ operator "<<" $> JSShl, operator ">>" $> JSShr ]
      , InfixL  [ operator "<=" $> JSLe, operator "<" $> JSLt
                , operator ">=" $> JSGe, operator ">" $> JSGt ]
      , InfixL  [ operator "==" $> JSEq, operator "!=" $> JSNe ]
      , InfixL  [ try (operator "&") $> JSBitAnd ]
      , InfixL  [ operator "^" $> JSBitXor ]
      , InfixL  [ try (operator "|") $> JSBitOr ]
      , InfixL  [ operator "&&" $> JSAnd ]
      , InfixL  [ operator "||" $> JSOr ]
      ]
      (JSUnary <$> memOrCon)
    memOrCon :: Parser JSUnary
    memOrCon = keyword "delete" *> (JSDel <$> member)
           <|> keyword "new" *> (JSCons <$> con)
           <|> JSMember <$> member
    con :: Parser JSCons
    con = liftA2 JSQual (keyword "this" $> "this") (dot *> conCall) <|> conCall
    conCall :: Parser JSCons
    conCall = identifier <**>
                (dot *> (flip JSQual <$> conCall)
             <|> flip JSConCall <$> parens (commaSep asgn)
             <|> pure (\name -> JSConCall name []))
    member :: Parser JSMember
    member = primaryExpr <**>
                (flip JSCall <$> parens (commaSep asgn)
             <|> flip JSIndex <$> brackets expr
             <|> dot *> ((flip JSAccess) <$> member)
             <|> pure JSPrimExp)
    primaryExpr :: Parser JSAtom
    primaryExpr = JSParens <$> parens expr
              <|> JSArray <$> brackets (commaSep asgn)
              <|> JSId <$> identifier
              <|> either JSInt JSFloat <$> naturalOrFloat
              <|> JSString <$> stringLiteral
              <|> JSTrue <$ keyword "true"
              <|> JSFalse <$ keyword "false"
              <|> JSNull <$ keyword "null"
              <|> JSThis <$ keyword "this"

    -- Token Parsers
    space :: Parser ()
    space = void (satisfy isSpace)
    whitespace :: Parser ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser String
    identifier = try ((identStart <:> many identLetter) >?> jsUnreservedName) <* whitespace
    naturalOrFloat :: Parser (Either Int Double)
    naturalOrFloat = natFloat <* whitespace

    -- Nonsense to deal with floats and ints
    natFloat :: Parser (Either Int Double)
    natFloat = char '0' *> zeroNumFloat <|> decimalFloat

    zeroNumFloat :: Parser (Either Int Double)
    zeroNumFloat = Left <$> (hexadecimal <|> octal)
               <|> decimalFloat
               <|> (fromMaybeP (fractFloat <*> pure 0) empty)
               <|> pure (Left 0)

    decimalFloat :: Parser (Either Int Double)
    decimalFloat = fromMaybeP (decimal <**> (option (Just . Left) fractFloat)) empty

    fractFloat :: Parser (Int -> Maybe (Either Int Double))
    fractFloat = f <$> fractExponent
      where
        f g x = fmap Right (g x)

    fractExponent :: Parser (Int -> Maybe Double)
    fractExponent = f <$> fraction <*> option "" exponent'
                <|> f <$> pure "" <*> exponent'
      where
        f fract exp n = readMaybe (show n ++ fract ++ exp)

    fraction :: Parser [Char]
    fraction = char '.' <:> some (oneOf ['0'..'9'])

    exponent' :: Parser [Char]
    exponent' = ('e' :) <$> (oneOf "eE"
             *> ((((:) <$> oneOf "+-") <|> pure id)
             <*> (show <$> decimal)))

    decimal :: Parser Int
    decimal = number 10 (oneOf ['0'..'9'])
    hexadecimal = oneOf "xX" *> number 16 (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number 8 (oneOf ['0'..'7'])

    number :: Int -> Parser Char -> Parser Int
    number base = pfoldl1 (\x d -> base * x + digitToInt d) 0

    stringLiteral :: Parser String
    stringLiteral = catMaybes <$> between (token "\"") (token "\"") (many stringChar) <* whitespace
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
    oneLineComment = void (token "//" *> skipMany (satisfy (/= '\n')))

    multiLineComment :: Parser ()
    multiLineComment =
      let inComment = void (token "*/")
                  <|> skipSome (satisfy (/= '*')) *> inComment
                  <|> char '*' *> inComment
      in token "/*" *> inComment

    identStart = satisfy jsIdentStart
    identLetter = satisfy jsIdentLetter
    notIdentLetter = peekChar >?> (maybe True (not . jsIdentLetter))
    notOpLetter = peekChar >?> (maybe True (notInClass "+-*/=<>!~&|.%^"))

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser (Maybe Char)
    stringChar = Just <$> satisfy jsStringLetter <|> stringEscape

    stringEscape :: Parser (Maybe Char)
    stringEscape = token "\\" *> (token "&" $> Nothing
                              <|> spaces *> token "\\" $> Nothing
                              <|> Just <$> escapeCode)

    escapeCode :: Parser Char
    escapeCode = match escChrs (oneOf escChrs) escCode empty
      where
        escCode 'a' = pure ('\a')
        escCode 'b' = pure ('\b')
        escCode 'f' = pure ('\f')
        escCode 'n' = pure ('\n')
        escCode 't' = pure ('\t')
        escCode 'v' = pure ('\v')
        escCode '\\' = pure ('\\')
        escCode '"' = pure ('"')
        escCode '\'' = pure ('\'')
        escCode '^' = (\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) <$> satisfy isUpper
        escCode 'A' = token "CK" $> ('\ACK')
        escCode 'B' = token "S" $> ('\BS') <|> token "EL" $> ('\BEL')
        escCode 'C' = token "R" $> ('\CR') <|> token "AN" $> ('\CAN')
        escCode 'D' = token "C" *> (token "1" $> ('\DC1')
                             <|> token "2" $> ('\DC2')
                             <|> token "3" $> ('\DC3')
                             <|> token "4" $> ('\DC4'))
               <|> token "EL" $> ('\DEL')
               <|> token "LE" $> ('\DLE')
        escCode 'E' = token "M" $> ('\EM')
               <|> token "T" *> (token "X" $> ('\ETX')
                             <|> token "B" $> ('\ETB'))
               <|> token "SC" $> ('\ESC')
               <|> token "OT" $> ('\EOT')
               <|> token "NQ" $> ('\ENQ')
        escCode 'F' = token "F" $> ('\FF') <|> token "S" $> ('\FS')
        escCode 'G' = token "S" $> ('\GS')
        escCode 'H' = token "T" $> ('\HT')
        escCode 'L' = token "F" $> ('\LF')
        escCode 'N' = token "UL" $> ('\NUL') <|> token "AK" $> ('\NAK')
        escCode 'R' = token "S" $> ('\RS')
        escCode 'S' = token "O" *> option (('\SO')) (token "H" $> ('\SOH'))
               <|> token "I" $> ('\SI')
               <|> token "P" $> ('\SP')
               <|> token "TX" $> ('\STX')
               <|> token "YN" $> ('\SYN')
               <|> token "UB" $> ('\SUB')
        escCode 'U' = token "S" $> ('\US')
        escCode 'V' = token "T" $> ('\VT')
        -- TODO numeric
        escCode _ = empty--error "numeric escape codes not supported"