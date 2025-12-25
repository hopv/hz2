
{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let op = "+" | "-" | "*" | "/"
let pred = "<=" | "<" | ">" | ">="

rule read = parse
  | white { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | "(*"  { comments 0 lexbuf }
  | "("   { LPAREN }
  | ")"   { RPAREN }
  | "["   { LBRACKET }
  | "]"   { RBRACKET }
  | "{"   { LBRACE }
  | "}"   { RBRACE }
  | ","   { COMMA }
  | ":"   { COLLON }
  | ";"   { SEMICOLLON }
  | "if"   { IF }
  | "then"   { THEN }
  | "else"   { ELSE }
  | "="   { EQUAL }
  | "o"   { OTYPE }
  | "int"   { INTTYPE }
  | "->"   { ARROW }
  | "=>"   { DARROW }
  | "not"  { NOT }
  | pred    { PRED (Lexing.lexeme lexbuf) }  
  | op    { OP (Lexing.lexeme lexbuf) }
  | id    { ID (Lexing.lexeme lexbuf) }
  | int   { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof   { EOF }
and comments level = parse
  | "*)" { if level = 0 then read lexbuf else comments (level - 1) lexbuf }
  | "(*" { comments (level + 1) lexbuf }
  | eof  { raise End_of_file }
  | _    { comments level lexbuf }