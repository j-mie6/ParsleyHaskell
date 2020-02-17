module CommonFunctions where

import Data.Int
import Data.Char (ord, chr, isAlpha, isAlphaNum, isSpace, isUpper, isDigit, digitToInt)
import Data.Set (fromList, member)

data Pred = And Pred Pred | Not Pred | T | F deriving Show
data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving Show

data Tape a = Tape [a] a [a]

evalBf :: [BrainFuckOp] -> IO ()
evalBf prog = go (Tape (repeat 0) 0 (repeat 0)) prog >> return ()
  where
    evalOp :: BrainFuckOp -> Tape Int32 -> IO (Tape Int32)
    evalOp RightPointer tape =                      return (right tape)
    evalOp LeftPointer  tape =                      return (left tape)
    evalOp Increment    tape = let x = read tape in return (write (succ x) tape)
    evalOp Decrement    tape = let x = read tape in return (write (pred x) tape)
    evalOp Output       tape = let x = read tape in do print (chr (fromEnum x)); return tape 
    evalOp Input        tape =                      do x <- getChar; return (write (toEnum (ord x)) tape)
    evalOp (Loop p)     tape = let x = read tape in if x == 0 then return tape
                                                    else do tape' <- go tape p
                                                            if read tape' /= 0 then evalOp (Loop p) tape'
                                                            else return tape'

    go :: Tape Int32 -> [BrainFuckOp] -> IO (Tape Int32)
    go tape [] = return tape
    go tape (op:ops) = do tape' <- evalOp op tape; go tape' ops

    right :: Tape a -> Tape a
    right (Tape ls x (r:rs)) = Tape (x:ls) r rs
    left :: Tape a -> Tape a
    left (Tape (l:ls) x rs) = Tape ls l (x:rs)
    read :: Tape a -> a
    read (Tape _ x _) = x
    write :: a -> Tape a -> Tape a
    write x (Tape ls _ rs) = Tape ls x rs

{- JAVASCRIPT -}
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

nandIdentStart :: Char -> Bool
nandIdentStart c = isAlpha c || c == '_'

nandIdentLetter :: Char -> Bool
nandIdentLetter c = isAlphaNum c || c == '_'

nandUnreservedName :: String -> Bool
nandUnreservedName = \s -> not (member s keys)
  where
    keys = fromList ["if", "else", "while",
                     "function", "var"]