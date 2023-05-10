module Parsley.Combinator.Parsers where

import Prelude hiding ((*>), (<*))

import Parsley
import Parsley.Combinator
import Parsley.Char

factoring :: Parser [String]
factoring = many $ (more *>) $
      string "if" <* notFollowedBy (oneOf ['a'..'z'])
  <|> string "while" <* notFollowedBy (oneOf ['a'..'z'])
  <|> string "return" <* notFollowedBy (oneOf ['a'..'z'])
  <|> string "continue" <* notFollowedBy (oneOf ['a'..'z'])
  <|> string "break" <* notFollowedBy (oneOf ['a'..'z'])
  <|> string "for" <* notFollowedBy (oneOf ['a'..'z'])
  <|> q
  <|> q
  where
    q = string "hello!" <* notFollowedBy (oneOf ['a'..'z'])
