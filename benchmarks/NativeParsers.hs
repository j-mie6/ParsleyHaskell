module NativeParsers where
import CommonFunctions

brainfuck :: String -> Maybe [BrainFuckOp]
brainfuck input = 
  let walk :: String -> [BrainFuckOp] -> ([BrainFuckOp], String)
      walk [] acc            = (reverse acc, [])
      walk input@(']':_) acc = (reverse acc, input)
      walk (c:rest) acc      = case c of
        '>' -> walk rest (RightPointer:acc)
        '<' -> walk rest (LeftPointer:acc)
        '+' -> walk rest (Increment:acc)
        '-' -> walk rest (Decrement:acc)
        '.' -> walk rest (Output:acc)
        ',' -> walk rest (Input:acc)
        '[' -> let (body, rest') = loop rest in walk rest' (Loop body:acc)
        _   -> walk rest acc
      loop :: String -> ([BrainFuckOp], String)
      loop input = let (body, rest) = walk input []
                   in case rest of
                     ']':rest' -> (body, rest')
                     _ -> error "Unclosed loop"
  in case walk input [] of
    (res, []) -> Just res
    _         -> error "] closes a loop, but no loop was opened"
        
tailTest :: String -> Maybe Char
tailTest [] = Nothing
tailTest (c:cs) = case c of
  'a' -> tailTest cs
  'b' -> Just 'b'
  _   -> Nothing