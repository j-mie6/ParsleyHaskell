module Parsley.Char.Parsers where

import Parsley (Parser)
import Parsley.Char (oneOf)

abc :: Parser Char
abc = oneOf ['a', 'b', 'c']

nothing :: Parser Char
nothing = oneOf []
