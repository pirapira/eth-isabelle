
{
  open Lexing
  open Parsr
  exception SyntaxError of string
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let comment = "//" (_ # ['\r' '\n'])* newline

rule read =
  parse
  | white    { read lexbuf }
  | comment  { new_line lexbuf; read lexbuf }
  | newline  { new_line lexbuf; read lexbuf }
  | "switch" { SWITCH }
  | "default"  { DEFAULT }
  | "case"     { CASE }
  | "function" { FUNCTION }
  | "let" { LET }
  | "for" { FOR }
  | "break" { BREAK }
  | "continue" { CONTINUE }
  | ":=" { ASSIGN}
  | "," { COMMA }
  | ":" { COLON }
  | "->" { ARROW }
  | "bool" { BOOL }
  | "false" { FALSE }
  | "true" { TRUE }
  | "s8" { S8 }
  | "u8" { U8 }
  | "s32" { S32 }
  | "u32" { U32 }
  | "s64" { S64 }
  | "u64" { U64 }
  | "s128" { S128 }
  | "u128" { U128 }
  | "s256" { S256 }
  | "u256" { U256 }

