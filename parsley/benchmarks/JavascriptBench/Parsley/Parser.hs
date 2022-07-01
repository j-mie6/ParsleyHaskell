{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module JavascriptBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import Parsley.Char (token, oneOf, noneOf, digit)
import Parsley.Combinator (eof)
import Parsley.Fold (skipMany, skipSome, sepBy, sepBy1, somel, chainl1)
import Parsley.Precedence (precHomo, ops, Fixity(InfixL, Prefix, Postfix))
import Parsley.Defunctionalized (Defunc(CONS, ID, LIFTED, LAM_S), pattern FLIP_H, pattern COMPOSE_H)
import JavascriptBench.Shared
import Data.Char (isSpace, isUpper, digitToInt, isDigit)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)
import Control.Monad (liftM)
import Language.Haskell.TH.Syntax (Lift(..))

#define QQ(x) (makeQ (x) [|| x ||])

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
    element = keyword "function" *> liftA3 QQ(JSFunction) identifier (parens (commaSep identifier)) compound
          <|> QQ(JSStm) <$> stmt
    compound :: Parser JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser JSStm
    stmt = semi $> QQ(JSSemi)
       <|> keyword "if" *> liftA3 QQ(JSIf) parensExpr stmt (maybeP (keyword "else" *> stmt))
       <|> keyword "while" *> liftA2 QQ(JSWhile) parensExpr stmt
       <|> (keyword "for" *> parens
               (try (liftA2 QQ(JSForIn) varsOrExprs (keyword "in" *> expr))
            <|> liftA3 QQ(JSFor) (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> keyword "break" $> QQ(JSBreak)
       <|> keyword "continue" $> QQ(JSContinue)
       <|> keyword "with" *> liftA2 QQ(JSWith) parensExpr stmt
       <|> keyword "return" *> (QQ(JSReturn) <$> optExpr)
       <|> QQ(JSBlock) <$> compound
       <|> QQ(JSNaked) <$> varsOrExprs
    varsOrExprs :: Parser (Either [JSVar] JSExpr)
    varsOrExprs = keyword "var" *> commaSep1 variable <+> expr
    variable :: Parser JSVar
    variable = liftA2 QQ(JSVar) identifier (maybeP (symbol '=' *> asgn))
    parensExpr :: Parser JSExpr
    parensExpr = parens expr
    optExpr :: Parser (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser JSExpr
    expr = commaSep1 asgn
    asgn :: Parser JSExpr'
    asgn = chainl1 condExpr (symbol '=' $> QQ(JSAsgn))
    condExpr :: Parser JSExpr'
    condExpr = liftA2 QQ(jsCondExprBuild) expr' (maybeP ((symbol '?' *> asgn) <~> (symbol ':' *> asgn)))
    expr' :: Parser JSExpr'
    expr' = precHomo (QQ(JSUnary) <$> memOrCon)
      [ ops Prefix  [ operator "--" $> QQ(jsDec), operator "++" $> QQ(jsInc)
                    , operator "-" $> QQ(jsNeg), operator "+" $> QQ(jsPlus)
                    , operator "~" $> QQ(jsBitNeg), operator "!" $> QQ(jsNot) ]
      , ops Postfix [ operator "--" $> QQ(jsDec), operator "++" $> QQ(jsInc) ]
      , ops InfixL  [ operator "*" $> QQ(JSMul), operator "/" $> QQ(JSDiv)
                    , operator "%" $> QQ(JSMod) ]
      , ops InfixL  [ operator "+" $> QQ(JSAdd), operator "-" $> QQ(JSSub) ]
      , ops InfixL  [ operator "<<" $> QQ(JSShl), operator ">>" $> QQ(JSShr) ]
      , ops InfixL  [ operator "<=" $> QQ(JSLe), operator "<" $> QQ(JSLt)
                    , operator ">=" $> QQ(JSGe), operator ">" $> QQ(JSGt) ]
      , ops InfixL  [ operator "==" $> QQ(JSEq), operator "!=" $> QQ(JSNe) ]
      , ops InfixL  [ try (operator "&") $> QQ(JSBitAnd) ]
      , ops InfixL  [ operator "^" $> QQ(JSBitXor) ]
      , ops InfixL  [ try (operator "|") $> QQ(JSBitOr) ]
      , ops InfixL  [ operator "&&" $> QQ(JSAnd) ]
      , ops InfixL  [ operator "||" $> QQ(JSOr) ]
      ]
    memOrCon :: Parser JSUnary
    memOrCon = keyword "delete" *> (QQ(JSDel) <$> member)
           <|> keyword "new" *> (QQ(JSCons) <$> con)
           <|> QQ(JSMember) <$> member
    con :: Parser JSCons
    con = liftA2 QQ(JSQual) (keyword "this" $> QQ("this")) (dot *> conCall) <|> conCall
    conCall :: Parser JSCons
    conCall = identifier <**>
                (dot *> (FLIP_H QQ(JSQual) <$> conCall)
             <|> FLIP_H QQ(JSConCall) <$> parens (commaSep asgn)
             <|> pure QQ((`JSConCall` [])))
    member :: Parser JSMember
    member = primaryExpr <**>
                (FLIP_H QQ(JSCall) <$> parens (commaSep asgn)
             <|> FLIP_H QQ(JSIndex) <$> brackets expr
             <|> dot *> (FLIP_H QQ(JSAccess) <$> member)
             <|> pure QQ(JSPrimExp))
    primaryExpr :: Parser JSAtom
    primaryExpr = QQ(JSParens) <$> parens expr
              <|> QQ(JSArray) <$> brackets (commaSep asgn)
              <|> QQ(JSId) <$> identifier
              <|> QQ(either JSInt JSFloat) <$> naturalOrFloat
              <|> QQ(JSString) <$> stringLiteral
              <|> QQ(JSTrue) <$ keyword "true"
              <|> QQ(JSFalse) <$ keyword "false"
              <|> QQ(JSNull) <$ keyword "null"
              <|> QQ(JSThis) <$ keyword "this"

    -- Token Parsers
    space :: Parser ()
    space = void (satisfy QQ(isSpace))
    whitespace :: Parser ()
    whitespace = skipMany (spaces <|> oneLineComment <|> multiLineComment)
    keyword :: String -> Parser ()
    keyword s = try (string s *> notIdentLetter) *> whitespace
    operator :: String -> Parser ()
    operator op = try (string op *> notOpLetter) *> whitespace
    identifier :: Parser String
    identifier = try ((identStart <:> many identLetter) >?> QQ(jsUnreservedName)) <* whitespace
    naturalOrFloat :: Parser (Either Int Double)
    naturalOrFloat = natFloat <* whitespace

    -- Nonsense to deal with floats and ints
    natFloat :: Parser (Either Int Double)
    natFloat = char '0' *> zeroNumFloat <|> decimalFloat

    zeroNumFloat :: Parser (Either Int Double)
    zeroNumFloat = QQ(Left) <$> (hexadecimal <|> octal)
               <|> decimalFloat
               <|> fromMaybeP (fractFloat <*> pure (LIFTED 0)) empty
               <|> pure QQ(Left 0)

    decimalFloat :: Parser (Either Int Double)
    decimalFloat = fromMaybeP (decimal <**> option (COMPOSE_H QQ(Just) QQ(Left)) fractFloat) empty

    fractFloat :: Parser (Int -> Maybe (Either Int Double))
    fractFloat = QQ(\g x -> liftM Right (g x)) <$> fractExponent

    fractExponent :: Parser (Int -> Maybe Double)
    fractExponent = f <$> fraction <*> option QQ("") exponent'
                <|> g <$> exponent'
      where
        f = QQ(\fract exp n -> readMaybe (show n ++ fract ++ exp))
        g = QQ(\exp n -> readMaybe (show n ++ exp))

    fraction :: Parser [Char]
    fraction = char '.' <:> some digit

    exponent' :: Parser [Char]
    exponent' = QQ(('e' :)) <$> (oneOf "eE"
             *> (((CONS <$> oneOf "+-") <|> pure ID)
             <*> (QQ(show) <$> decimal)))

    decimal :: Parser Int
    decimal = number 10 digit
    hexadecimal = oneOf "xX" *> number 16 (oneOf (['a'..'f'] ++ ['A'..'F'] ++ ['0'..'9']))
    octal = oneOf "oO" *> number 8 (oneOf ['0'..'7'])

    number :: Int -> Parser Char -> Parser Int
    number base digit = somel addDigit (LIFTED 0) digit
      where
        addDigit = QQ(\x d -> base * x + digitToInt d)

    stringLiteral :: Parser String
    stringLiteral = QQ(catMaybes) <$> between (token "\"") (token "\"") (many stringChar) <* whitespace
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
    oneLineComment = void (token "//" *> skipMany (satisfy QQ((/= '\n'))))

    multiLineComment :: Parser ()
    multiLineComment =
      let inComment = void (token "*/")
                  <|> skipSome (noneOf "*") *> inComment
                  <|> char '*' *> inComment
      in token "/*" *> inComment

    identStart = satisfy QQ(jsIdentStart)
    identLetter = satisfy QQ(jsIdentLetter)
    notIdentLetter = notFollowedBy identLetter
    notOpLetter = notFollowedBy (oneOf "+-*/=<>!~&|.%^")

    escChrs :: [Char]
    escChrs = "abfntv\\\"'0123456789xo^ABCDEFGHLNRSUV"

    stringChar :: Parser (Maybe Char)
    stringChar = QQ(Just) <$> satisfy QQ(jsStringLetter) <|> stringEscape

    stringEscape :: Parser (Maybe Char)
    stringEscape = token "\\" *> (token "&" $> QQ(Nothing)
                              <|> spaces *> token "\\" $> QQ(Nothing)
                              <|> QQ(Just) <$> escapeCode)

    escapeCode :: Parser Char
    escapeCode = match escChrs (oneOf escChrs) escCode empty
      where
        escCode 'a' = pure QQ('\a')
        escCode 'b' = pure QQ('\b')
        escCode 'f' = pure QQ('\f')
        escCode 'n' = pure QQ('\n')
        escCode 't' = pure QQ('\t')
        escCode 'v' = pure QQ('\v')
        escCode '\\' = pure QQ('\\')
        escCode '"' = pure QQ('"')
        escCode '\'' = pure QQ('\'')
        escCode '^' = QQ(\c -> toEnum (fromEnum c - fromEnum 'A' + 1)) <$> satisfy QQ(isUpper)
        escCode 'A' = token "CK" $> QQ('\ACK')
        escCode 'B' = token "S" $> QQ('\BS') <|> token "EL" $> QQ('\BEL')
        escCode 'C' = token "R" $> QQ('\CR') <|> token "AN" $> QQ('\CAN')
        escCode 'D' = token "C" *> (token "1" $> QQ('\DC1')
                             <|> token "2" $> QQ('\DC2')
                             <|> token "3" $> QQ('\DC3')
                             <|> token "4" $> QQ('\DC4'))
               <|> token "EL" $> QQ('\DEL')
               <|> token "LE" $> QQ('\DLE')
        escCode 'E' = token "M" $> QQ('\EM')
               <|> token "T" *> (token "X" $> QQ('\ETX')
                             <|> token "B" $> QQ('\ETB'))
               <|> token "SC" $> QQ('\ESC')
               <|> token "OT" $> QQ('\EOT')
               <|> token "NQ" $> QQ('\ENQ')
        escCode 'F' = token "F" $> QQ('\FF') <|> token "S" $> QQ('\FS')
        escCode 'G' = token "S" $> QQ('\GS')
        escCode 'H' = token "T" $> QQ('\HT')
        escCode 'L' = token "F" $> QQ('\LF')
        escCode 'N' = token "UL" $> QQ('\NUL') <|> token "AK" $> QQ('\NAK')
        escCode 'R' = token "S" $> QQ('\RS')
        escCode 'S' = token "O" *> option QQ('\SO') (token "H" $> QQ('\SOH'))
               <|> token "I" $> QQ('\SI')
               <|> token "P" $> QQ('\SP')
               <|> token "TX" $> QQ('\STX')
               <|> token "YN" $> QQ('\SYN')
               <|> token "UB" $> QQ('\SUB')
        escCode 'U' = token "S" $> QQ('\US')
        escCode 'V' = token "T" $> QQ('\VT')
        -- TODO numeric
        escCode _ = empty--error "numeric escape codes not supported"
