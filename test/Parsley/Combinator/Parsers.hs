module Parsley.Combinator.Parsers where

import Parsley (Parser)
import Parsley.Combinator (oneOf)

abc :: Parser Char
abc = oneOf ['a', 'b', 'c']

nothing :: Parser Char
nothing = oneOf []