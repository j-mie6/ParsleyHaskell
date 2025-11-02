{-# LANGUAGE TupleSections #-}
module ABCBench.Gigaparsec.Parser where

import Text.Gigaparsec
import Text.Gigaparsec.Combinator
import Text.Gigaparsec.Char
import Text.Gigaparsec.State



{- manyCount :: Parsec a -> Parsec ([a], Int)
manyCount p = go mempty 0 p
    where
        go :: [a] -> Int -> Parsec a -> Parsec ([a], Int)
        go xs count p = (p >>= (\x -> go (x:xs) (count + 1) p)) <|> pure (xs, count)

abc :: Parsec ()
abc = count (char 'a') >>= \count -> exactly count (char 'b') *> exactly count (char 'c')  *> eof

abcWithRef :: Parsec ()
abcWithRef =  make 0 $ \n -> many (char 'a' <* update n (+1))
                            *> downTo0 n (char 'b')
                            *> downTo0 n (char 'c') 
                            *> eof
                        where downTo0 n p = forP' (get n) (pure (> 0)) (pure (subtract 1)) (\i -> p) -}


abc :: Parsec ()
abc = count (char 'a') >>= \count -> exactly count (char 'b') *> exactly count (char 'c')  *> eof

abcWithRef :: Parsec ()
abcWithRef =  make 0 $ \n -> skipMany (char 'a' <* update n (+1))
                                *> downTo0 n (char 'b')
                                *> downTo0 n (char 'c')
                                *> eof
                        where downTo0 n = forP_ (get n) (pure (> 0)) (pure (subtract 1))
{-
 AsAndBsAndCs <- &(AsAndBs 'c') AsAndCs !.
AsAndBs      <- 'a' AsAndBs 'b' / epsilon
AsAndCs      <- 'a' AsAndCs 'c' / 'b'*

1:18

lazy val AsAndBs: Parsley[Unit] = optional(atomic('a' ~> AsAndBs <~ 'b'))
    lazy val AsAndCs: Parsley[Unit] = atomic('a' ~> AsAndCs <~ 'c') | many('b').void
    val AsAndBsAndCs = lookAhead(AsAndBs ~> 'c') ~> AsAndCs ~> eof
 -}
abcPEG :: Parsec ()
abcPEG = asbscs
    where
        asbscs = lookAhead (asbs *> char 'c') *> ascs *> eof
        ascs = (char 'a' *> ascs <* char 'c') <|> skipMany (char 'b')
        asbs = optional (atomic (char 'a' *> asbs <* char 'b'))