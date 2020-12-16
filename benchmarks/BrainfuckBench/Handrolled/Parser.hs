module BrainfuckBench.Handrolled.Parser where
import BrainfuckBench.Shared

brainfuck :: String -> Maybe [BrainFuckOp]
brainfuck input =
  let walk :: String -> [BrainFuckOp] -> Maybe ([BrainFuckOp], String)
      walk [] acc            = return (reverse acc, [])
      walk input@(']':_) acc = return (reverse acc, input)
      walk (c:rest) acc      = case c of
        '>' -> walk rest (RightPointer:acc)
        '<' -> walk rest (LeftPointer:acc)
        '+' -> walk rest (Increment:acc)
        '-' -> walk rest (Decrement:acc)
        '.' -> walk rest (Output:acc)
        ',' -> walk rest (Input:acc)
        '[' -> do (body, rest') <- loop rest; walk rest' (Loop body:acc)
        _   -> walk rest acc
      loop :: String -> Maybe ([BrainFuckOp], String)
      loop input = do
        (body, rest) <- walk input []
        case rest of
          ']':rest' -> return (body, rest')
          _ -> fail "unclosed loop"
  in  do
    (res, []) <- walk input []
    return res