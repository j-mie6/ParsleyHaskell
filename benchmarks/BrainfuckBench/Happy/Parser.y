{
module BrainfuckBench.Happy.Parser where
import BrainfuckBench.Shared (BrainFuckOp(..))
}

%name brainfuck Bf
%tokentype { Char }
%error { const Nothing }
%monad { Maybe }

%token
    inc { '+' }
    dec { '-' }
    out { '.' }
    in  { ',' }
    lft { '<' }
    rht { '>' }
    lb  { '[' }
    rb  { ']' }
    ws  { $$  }

%%

Bf :: { [BrainFuckOp] }
Bf : inc Bf      { Increment    : $2 }
   | dec Bf      { Decrement    : $2 }
   | out Bf      { Output       : $2 }
   | in  Bf      { Input        : $2 }
   | lft Bf      { LeftPointer  : $2 }
   | rht Bf      { RightPointer : $2 }
   | lb Bf rb Bf { Loop $2 : $4 }
   | ws Bf       { $2 }
   | { [] }
