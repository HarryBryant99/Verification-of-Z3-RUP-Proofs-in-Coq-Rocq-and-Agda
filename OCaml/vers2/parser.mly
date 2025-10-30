%{
open Proven_sat_checker
open Types

let char_list_of_string (s : string) : char list =
  List.of_seq (String.to_seq s)

let rec to_listZ3_Formula (lst : z3_Formula list) : listZ3_Formula =
  match lst with
  | [] -> Lnil
  | x :: xs -> Lcons (x, to_listZ3_Formula xs)

let rec normalize f =
  match f with
  | Not inner ->
      begin match normalize inner with
      | Not inner2 -> normalize inner2  (* remove double negation *)
      | simplified -> Not simplified
      end
  | And lst -> And (normalize_list lst)
  | Or lst -> Or (normalize_list lst)
  | Imply (a, b) -> Imply (normalize a, normalize b)
  | Z3var _ -> f

and normalize_list lst =
  match lst with
  | Lnil -> Lnil
  | Lcons (x, xs) -> Lcons (normalize x, normalize_list xs)

let item_counter = ref 0
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

(*
item_list:
  | item { [$1] }
  | item item_list { $1 :: $2 }
*)

item_list:
  | item {
      incr item_counter;
      if !item_counter mod 10000 = 0 then
        Printf.printf "Parsed %d items\n%!" !item_counter;
      [$1]
    }
  | item item_list {
      incr item_counter;
      if !item_counter mod 10000 = 0 then
        Printf.printf "Parsed %d items\n%!" !item_counter;
      $1 :: $2
    }

item:
  | TSEITIN LPAREN formula_list RPAREN LBRACK RBRACK LBRACK formula_list RBRACK
      { Tseitin ($3, $8) }
  | ASSUMPTION LBRACK RBRACK LBRACK formula_list RBRACK
      { Assumption $5 }
  | RUP LBRACK RBRACK LBRACK formula_list RBRACK
      { Rup $5 }

formula_list:
  | formula_list_nonempty { $1 }
  |                       { Lnil }

formula_list_nonempty:
  | formula {
      let simplified = normalize $1 in
      Lcons (simplified, Lnil)
    }

  | formula COMMA formula_list_nonempty {
      let simplified = normalize $1 in
      Lcons (simplified, $3)
    }

(*
formula_list_nonempty:
  | formula {
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3var v -> Some (depth, Z3var v)
        | And lst -> Some (depth, And lst)
        | Or lst -> Some (depth, Or lst)
        | Imply (a, b) -> Some (depth, Imply (a, b))
      in
      match unwrap_not $1 0 with
      | Some (depth, pf) ->
          let final_formula =
            if depth mod 2 = 0 then pf else Not pf
          in
          Lcons (final_formula, Lnil)
      | None -> failwith "Unsupported formula structure in literal"
    }

  | formula COMMA formula_list_nonempty {
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3var v -> Some (depth, Z3var v)
        | And lst -> Some (depth, And lst)
        | Or lst -> Some (depth, Or lst)
        | Imply (a, b) -> Some (depth, Imply (a, b))
      in
      let head =
        match unwrap_not $1 0 with
        | Some (depth, pf) ->
            if depth mod 2 = 0 then pf else Not pf
        | None -> failwith "Unsupported formula structure in literal"
      in
      Lcons (head, $3)
    }
*)

formula:
  | TRUE                        { Z3var (char_list_of_string "True") }
  | FALSE                       { Z3var (char_list_of_string "False") }
  | ATOM                        { Z3var $1 }
  | NOT LPAREN formula RPAREN   { Not $3 }
  | IMPLIES LPAREN formula COMMA formula RPAREN { Imply ($3, $5) }
  | AND LPAREN formula_list_expr RPAREN { And $3 }
  | OR LPAREN formula_list_expr RPAREN  { Or $3 }

formula_list_expr:
  | formula { Lcons ($1, Lnil) }
  | formula COMMA formula_list_expr { Lcons ($1, $3) }

