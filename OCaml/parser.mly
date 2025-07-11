%{
open Types

let char_list_of_string (s : string) : char list =
  List.of_seq (String.to_seq s)
%}

%token <char list> ATOM
%token TRUE FALSE
%token NOT IMPLIES AND OR
%token TSEITIN ASSUMPTION RUP
%token LPAREN RPAREN LBRACK RBRACK COMMA
%token EOF
%start start
%type <Types.item list> start

%%

start:
  | item_list EOF { $1 }

item_list:
  | item { [$1] }
  | item item_list { $1 :: $2 }

item:
  | TSEITIN LPAREN formula_list RPAREN LBRACK RBRACK LBRACK formula_list RBRACK
      { Tseitin ($3, $8) }
  | ASSUMPTION LBRACK RBRACK LBRACK formula_list RBRACK
      { Assumption $5 }
  | RUP LBRACK RBRACK LBRACK formula_list RBRACK
      { Rup $5 }

formula_list:
  | formula_list_nonempty { $1 }
  |                       { [] }

formula_list_nonempty:
  | formula {
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3Var v -> Some (depth, PosZ3Var v)
        | And lst -> Some (depth, PosAnd lst)
        | Or lst -> Some (depth, PosOr lst)
        | Imply lst -> Some (depth, PosImply lst)
        (*| _ -> None*)
      in
      match unwrap_not $1 0 with
      | Some (depth, pf) ->
          if depth mod 2 = 0 then [Pos pf] else [Neg pf]
      | None -> failwith "Unsupported formula structure in literal"
    }
  | formula COMMA formula_list_nonempty {
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3Var v -> Some (depth, PosZ3Var v)
        | And lst -> Some (depth, PosAnd lst)
        | Or lst -> Some (depth, PosOr lst)
        | Imply lst -> Some (depth, PosImply lst)
        (*| _ -> None*)
      in
      let head =
        match unwrap_not $1 0 with
        | Some (depth, pf) ->
            if depth mod 2 = 0 then Pos pf else Neg pf
        | None -> failwith "Unsupported formula structure in literal"
      in
      head :: $3
    }

formula:
  | TRUE                        { Z3Var (char_list_of_string "True") }
  | FALSE                       { Z3Var (char_list_of_string "False") }
  | ATOM                        { Z3Var $1 }
  | NOT LPAREN formula RPAREN   { Not $3 }
  | IMPLIES LPAREN formula COMMA formula RPAREN { Imply [$3; $5] }
  | AND LPAREN formula_list_expr RPAREN { And $3 }
  | OR LPAREN formula_list_expr RPAREN  { Or $3 }

formula_list_expr:
  | formula { [$1] }
  | formula COMMA formula_list_expr { $1 :: $3 }
