{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ParsleyTokenParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import Parsley.Fold (skipMany, skipSome, sepBy, sepBy1, pfoldl1, chainl1)
import Parsley.Precedence (precedence, monolith, prefix, postfix, infixR, infixL)
import CommonFunctions
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader)
import Control.Monad.Writer (WriterT, execWriterT, MonadWriter, tell)
import qualified Control.Applicative as App

deriving instance Lift JSElement
deriving instance Lift JSStm
deriving instance Lift JSVar
deriving instance Lift JSExpr'
deriving instance Lift JSUnary
deriving instance Lift JSMember
deriving instance Lift JSCons
deriving instance Lift JSAtom

deriving instance Lift JSToken
instance Token JSToken

javascript :: Parser JSToken JSProgram
javascript = many element <* token Eof
  where
    element :: Parser JSToken JSElement
    element = token TokenFunction *> liftA3 (code JSFunction) identifier (parens (commaSep identifier)) compound
          <|> code JSStm <$> stmt
    compound :: Parser JSToken JSCompoundStm
    compound = braces (many stmt)
    stmt :: Parser JSToken JSStm
    stmt = semi $> code JSSemi
       <|> token TokenIf *> liftA3 (code JSIf) parensExpr stmt (maybeP (token TokenElse *> stmt))
       <|> token TokenWhile *> liftA2 (code JSWhile) parensExpr stmt
       <|> (token TokenFor *> parens
               (try (liftA2 (code JSForIn) varsOrExprs (token TokenIn *> expr))
            <|> liftA3 (code JSFor) (maybeP varsOrExprs <* semi) (optExpr <* semi) optExpr)
           <*> stmt)
       <|> token TokenBreak $> code JSBreak
       <|> token TokenContinue $> code JSContinue
       <|> token TokenWith *> liftA2 (code JSWith) parensExpr stmt
       <|> token TokenReturn *> (code JSReturn <$> optExpr)
       <|> code JSBlock <$> compound
       <|> code JSNaked <$> varsOrExprs
    varsOrExprs :: Parser JSToken (Either [JSVar] JSExpr)
    varsOrExprs = token TokenVar *> commaSep1 variable <+> expr
    variable :: Parser JSToken JSVar
    variable = liftA2 (code JSVar) identifier (maybeP (token TokenAss *> asgn))
    parensExpr :: Parser JSToken JSExpr
    parensExpr = parens expr
    optExpr :: Parser JSToken (Maybe JSExpr)
    optExpr = maybeP expr
    expr :: Parser JSToken JSExpr
    expr = commaSep1 asgn
    asgn :: Parser JSToken JSExpr'
    asgn = chainl1 condExpr (token TokenAss $> code JSAsgn)
    condExpr :: Parser JSToken JSExpr'
    condExpr = liftA2 (code jsCondExprBuild) expr' (maybeP ((token TokenQuest *> asgn) <~> (token TokenColon *> asgn)))
    expr' :: Parser JSToken JSExpr'
    expr' = precedence (monolith
      [ prefix  [ token TokenDec $> code jsDec, token TokenInc $> code jsInc
                , token TokenSub $> code jsNeg, token TokenAdd $> code jsPlus
                , token TokenNeg $> code jsBitNeg, token TokenNot $> code jsNot ]
      , postfix [ token TokenDec $> code jsDec, token TokenInc $> code jsInc ]
      , infixL  [ token TokenMul $> code JSMul, token TokenDiv $> code JSDiv
                , token TokenMod $> code JSMod ]
      , infixL  [ token TokenAdd $> code JSAdd, token TokenSub $> code JSSub ]
      , infixL  [ token TokenShl $> code JSShl, token TokenShr $> code JSShr ]
      , infixL  [ token TokenLeq $> code JSLe, token TokenLt $> code JSLt
                , token TokenGeq $> code JSGe, token TokenGt $> code JSGt ]
      , infixL  [ token TokenEq $> code JSEq, token TokenNeq $> code JSNe ]
      , infixL  [ token TokenBAnd $> code JSBitAnd ]
      , infixL  [ token TokenXor $> code JSBitXor ]
      , infixL  [ token TokenBOr $> code JSBitOr ]
      , infixL  [ token TokenAnd $> code JSAnd ]
      , infixL  [ token TokenOr $> code JSOr ]
      ])
      (code JSUnary <$> memOrCon)
    memOrCon :: Parser JSToken JSUnary
    memOrCon = token TokenDelete *> (code JSDel <$> member)
           <|> token TokenNew *> (code JSCons <$> con)
           <|> code JSMember <$> member
    con :: Parser JSToken JSCons
    con = liftA2 (code JSQual) (token TokenThis $> code "this") (dot *> conCall) <|> conCall
    conCall :: Parser JSToken JSCons
    conCall = identifier <**>
                (dot *> (([flip (code JSQual)]) <$> conCall)
             <|> ([flip (code JSConCall)]) <$> parens (commaSep asgn)
             <|> pure (makeQ (\name -> JSConCall name []) [||\name -> JSConCall name []||]))
    member :: Parser JSToken JSMember
    member = primaryExpr <**>
                (([flip (code JSCall)]) <$> parens (commaSep asgn)
             <|> ([flip (code JSIndex)]) <$> brackets expr
             <|> dot *> (([flip (code JSAccess)]) <$> member)
             <|> pure (code JSPrimExp))
    primaryExpr :: Parser JSToken JSAtom
    primaryExpr = code JSParens <$> parens expr
              <|> code JSArray <$> brackets (commaSep asgn)
              <|> code JSId <$> identifier
              <|> ([either (code JSInt) (code JSFloat)]) <$> naturalOrFloat
              <|> code JSString <$> stringLiteral
              <|> code JSTrue <$ token TokenTrue
              <|> code JSFalse <$ token TokenFalse
              <|> code JSNull <$ token TokenNull
              <|> code JSThis <$ token TokenThis

    -- Token Parsers
    identifier :: Parser JSToken String
    identifier = code getId <$> satisfy (code isId)
    naturalOrFloat :: Parser JSToken (Either Int Double)
    naturalOrFloat = code getNumber <$> satisfy (code isNumber)
    stringLiteral :: Parser JSToken String
    stringLiteral = code getString <$> satisfy (code isString)

    parens :: Parser JSToken a -> Parser JSToken a
    parens = between (token TokenLParen) (token TokenRParen)
    brackets :: Parser JSToken a -> Parser JSToken a
    brackets = between (token TokenLBracket) (token TokenRBracket)
    braces :: Parser JSToken a -> Parser JSToken a
    braces = between (token TokenLBrace) (token TokenRBrace)
    dot :: Parser JSToken ()
    dot = void (token TokenDot)
    semi :: Parser JSToken ()
    semi = void (token TokenSemi)
    comma :: Parser JSToken ()
    comma = void (token TokenComma)
    commaSep :: Parser JSToken a -> Parser JSToken [a]
    commaSep p = sepBy p comma
    commaSep1 :: Parser JSToken a -> Parser JSToken [a]
    commaSep1 p = sepBy1 p comma

newtype Lexer a = Lexer (ReaderT String (WriterT [JSToken] Maybe) a)
  deriving (Functor, App.Applicative, App.Alternative, Monad, MonadReader String, MonadWriter [JSToken])

runLexer :: Lexer () -> String -> Maybe [JSToken]
runLexer (Lexer p) ts = execWriterT (runReaderT p ts)

lex :: String -> Maybe [JSToken]
lex cs = runLexer go cs
  where
    go :: Lexer ()
    go = lexer (\tok -> do tell [tok]; go)