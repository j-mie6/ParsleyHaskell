module JavascriptBench.Shared where

import Data.Char (isAlpha, isAlphaNum, isSpace, isUpper, isDigit, digitToInt)
import Data.Set (fromList, member)

type JSProgram = [JSElement]
type JSCompoundStm = [JSStm]
type JSExpr = [JSExpr']
data JSElement = JSFunction String [String] JSCompoundStm | JSStm JSStm deriving Show
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
           | JSNaked (Either [JSVar] JSExpr) deriving Show
data JSVar = JSVar String (Maybe JSExpr') deriving Show
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
             | JSUnary  JSUnary deriving Show
data JSUnary = JSPlus   JSUnary
             | JSNeg    JSUnary
             | JSBitNeg JSUnary
             | JSNot    JSUnary
             | JSInc    JSUnary
             | JSDec    JSUnary
             | JSNew    JSCons
             | JSDel    JSMember
             | JSMember JSMember
             | JSCons   JSCons deriving Show
jsPlus (JSUnary u)   = JSUnary (JSPlus u)
jsNeg (JSUnary u)    = JSUnary (JSNeg u)
jsBitNeg (JSUnary u) = JSUnary (JSBitNeg u)
jsNot (JSUnary u)    = JSUnary (JSNot u)
jsInc (JSUnary u)    = JSUnary (JSInc u)
jsDec (JSUnary u)    = JSUnary (JSDec u)
data JSMember = JSPrimExp JSAtom
              | JSAccess  JSAtom JSMember
              | JSIndex   JSAtom JSExpr
              | JSCall    JSAtom JSExpr deriving Show
data JSCons = JSQual String JSCons
            | JSConCall String JSExpr deriving Show
data JSAtom = JSParens JSExpr
            | JSArray  JSExpr
            | JSId     String
            | JSInt    Int
            | JSFloat  Double
            | JSString String
            | JSTrue
            | JSFalse
            | JSNull
            | JSThis deriving Show

jsCondExprBuild :: JSExpr' -> Maybe (JSExpr', JSExpr') -> JSExpr'
jsCondExprBuild c (Just (t, e)) = JSCond c t e
jsCondExprBuild c Nothing       = c

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
                     "this", "null", "return", "with"]

jsStringLetter :: Char -> Bool
jsStringLetter c = (c /= '"') && (c /= '\\') && (c > '\026')