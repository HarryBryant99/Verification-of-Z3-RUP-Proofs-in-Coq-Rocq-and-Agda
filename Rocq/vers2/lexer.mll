{
open Parser
let explode s = List.init (String.length s) (String.get s)
}

rule token = parse
  | [' ' '\t' '\n'] { token lexbuf }
  | "True"          { TRUE }
  | "False"         { FALSE }
  | "Not"           { NOT }
  | "Implies"       { IMPLIES }
  | "And"           { AND }
  | "Or"            { OR }
  | "tseitin"       { TSEITIN }
  | "assumption"    { ASSUMPTION }
  | "rup"           { RUP }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "["             { LBRACK }
  | "]"             { RBRACK }
  | ","             { COMMA }
  | ['a'-'z' 'A'-'Z' '0'-'9' '_' '-' '/']+ as id { ATOM (explode id) }
  | eof             { EOF }
  | _ as c { 
    Printf.eprintf "Unexpected character: '%c' (ASCII %d)\n" c (Char.code c);
    failwith ("lexing: unexpected character '" ^ String.make 1 c ^ "'") 
  }
