type token =
  | ATOM of (
# 33 "parser.mly"
        char list
# 6 "parser.mli"
)
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
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Types.item list
