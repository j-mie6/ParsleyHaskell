{-# LANGUAGE TypeFamilies
           , ScopedTypeVariables #-}

module JavascriptBench.Megaparsec.Parser where
import JavascriptBench.Shared
import Shared.Megaparsec.Extended
import Data.Char (isSpace, isUpper, digitToInt)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)

javascript :: forall s. (Stream s, Token s ~ Char) => Parser s JSProgram
javascript = whitespace *> many element <* eof
  where
    element :: Parser s JSElement
    element = keyword "function" *> liftA3 JSFunction identifier (parens (commaSep identifier)) compound
          <|> JSStm <$> stmt
    compound :: Parser s JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser s JSStm
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
    varsOrExprs :: Parser s (Either [JSVar] JSExpr)
    varsOrExprs = (keyword "var" *> commaSep1 variable) <+> expr
    variable :: Parser s JSVar
    variable = liftA2 JSVar identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser s JSExpr
    parensExpr = parens expr
    optExpr :: Parser s (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser s JSExpr
    expr = commaSep1 asgn
    asgn :: Parser s JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> JSAsgn)
    condExpr :: Parser s JSExpr'
    condExpr = liftA2 jsCondExprBuild expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser s JSExpr'
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
    memOrCon :: Parser s JSUnary
    memOrCon = keyword "delete" *> (JSDel <$> member)
           <|> keyword "new" *> (JSCons <$> con)
           <|> JSMember <$> member
    con :: Parser s JSCons
    con = liftA2 JSQual (keyword "this" $> "this") (dot *> conCall) <|> conCall
    conCall :: Parser s JSCons
    conCall = identifier <**>
                (dot *> (flip JSQual <$> conCall)
             <|> flip JSConCall <$> parens (commaSep asgn)
             <|> pure (\name -> JSConCall name []))
    member :: Parser s JSMember
    member = primaryExpr <**>
                (flip JSCall <$> parens (commaSep asgn)
             <|> flip JSIndex <$> brackets expr
             <|> dot *> ((flip JSAccess) <$> member)
             <|> pure JSPrimExp)
    primaryExpr :: Parser s JSAtom
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
    space :: Parser s ()
    space = void (satisfy isSpace)
    whitespace :: Parser s ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser s ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser s ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser s String
    identifier = try ((identStart <:> many identLetter) >?> jsUnreservedName) <* whitespace
    naturalOrFloat :: Parser s (Either Int Double)
    naturalOrFloat = natFloat <* whitespace

    -- Nonsense to deal with floats and ints
    natFloat :: Parser s (Either Int Double)
    natFloat = char '0' *> zeroNumFloat <|> decimalFloat

    zeroNumFloat :: Parser s (Either Int Double)
    zeroNumFloat = Left <$> (hexadecimal <|> octal)
               <|> decimalFloat
               <|> (fromMaybeP (fractFloat <*> pure 0) empty)
               <|> pure (Left 0)

    decimalFloat :: Parser s (Either Int Double)
    decimalFloat = fromMaybeP (decimal <**> (option (Just . Left) fractFloat)) empty

    fractFloat :: Parser s (Int -> Maybe (Either Int Double))
    fractFloat = f <$> fractExponent
      where
        f g x = fmap Right (g x)

    fractExponent :: Parser s (Int -> Maybe Double)
    fractExponent = f <$> fraction <*> option "" exponent'
                <|> f <$> pure "" <*> exponent'
      where
        f fract exp n = readMaybe (show n ++ fract ++ exp)

    fraction :: Parser s [Char]
    fraction = ('.' :) <$> (char '.'
            *> some (oneOf ['0'..'9']))

    exponent' :: Parser s [Char]
    exponent' = ('e' :) <$> (oneOf "eE"
             *> ((((:) <$> oneOf "+-") <|> pure id)
             <*> (show <$> decimal)))

    decimal :: Parser s Int
    decimal = number 10 (oneOf ['0'..'9'])
    hexadecimal = oneOf "xX" *> number 16 (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number 8 (oneOf ['0'..'7'])

    number :: Int -> Parser s Char -> Parser s Int
    number base = pfoldl1 (\x d -> base * x + digitToInt d) 0

    stringLiteral :: Parser s String
    stringLiteral = catMaybes <$> between (token "\"") (token "\"") (many stringChar) <* whitespace
    symbol :: Char -> Parser s Char
    symbol c = try (char c) <* whitespace
    parens :: Parser s a -> Parser s a
    parens = between (symbol '(') (symbol ')')
    brackets :: Parser s a -> Parser s a
    brackets = between (symbol '[') (symbol ']')
    braces :: Parser s a -> Parser s a
    braces = between (symbol '{') (symbol '}')
    dot :: Parser s Char
    dot = symbol '.'
    semi :: Parser s Char
    semi = symbol ';'
    comma :: Parser s Char
    comma = symbol ','
    commaSep :: Parser s a -> Parser s [a]
    commaSep p = sepBy p comma
    commaSep1 :: Parser s a -> Parser s [a]
    commaSep1 p = sepBy1 p comma

    -- Let bindings
    spaces :: Parser s ()
    spaces = skipSome space

    oneLineComment :: Parser s ()
    oneLineComment = void (token "//" *> skipMany (satisfy (/= '\n')))

    multiLineComment :: Parser s ()
    multiLineComment =
      let inComment = void (token "*/")
                  <|> skipSome (noneOf "/*") *> inComment
                  <|> oneOf "/*" *> inComment
      in token "/*" *> inComment

    identStart = satisfy jsIdentStart
    identLetter = satisfy jsIdentLetter
    notIdentLetter = notFollowedBy identLetter
    notOpLetter = notFollowedBy (oneOf "+-*/=<>!~&|.%^")

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser s (Maybe Char)
    stringChar = Just <$> satisfy jsStringLetter <|> stringEscape

    stringEscape :: Parser s (Maybe Char)
    stringEscape = token "\\" *> (token "&" $> Nothing
                              <|> spaces *> token "\\" $> Nothing
                              <|> Just <$> escapeCode)

    escapeCode :: Parser s Char
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