type token =
  | ATOM of (char list)
  | TRUE
  | FALSE
  | NOT
  | IMPLIES
  | AND
  | OR
  | TSEITIN
  | ASSUMPTION
  | RUP
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | COMMA
  | EOF

val start :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Rupchecker_z3_datatype.proofStep list
