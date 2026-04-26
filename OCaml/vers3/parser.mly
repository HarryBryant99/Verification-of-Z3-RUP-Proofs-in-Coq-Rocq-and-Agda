
%{
open Proven_checker_farkas_6
open Types

(* Convert string <-> char list *)
let char_list_of_string (s : string) : char list =
  List.of_seq (String.to_seq s)

let string_of_char_list (lst : char list) : string =
  String.of_seq (List.to_seq lst)

(* --- Symbol table: map atom strings to integer IDs --- *)
let atom_table : (string, int) Hashtbl.t = Hashtbl.create 1000
let next_id = ref 3

let () =
  Hashtbl.replace atom_table "False" 0;
  Hashtbl.replace atom_table "True" 1;
  Hashtbl.replace atom_table "defaultLiteral" 2

(*
let get_atom_id s =
  match Hashtbl.find_opt atom_table s with
  | Some id ->
      Printf.printf "Reuse %s -> %d\n" s id;
      id
  | None ->
      let id = !next_id in
      Printf.printf "New   %s -> %d\n" s id;
      Hashtbl.add atom_table s id;
      incr next_id;
      id
*)

let get_atom_id (s : string) : int =
  match Hashtbl.find_opt atom_table s with
  | Some id -> id
  | None ->
      let id = !next_id in
      Hashtbl.add atom_table s id;
      incr next_id;
      id

let reset_atom_table () =
  Hashtbl.reset atom_table;
  Hashtbl.replace atom_table "False" 0;
  Hashtbl.replace atom_table "True" 1;
  Hashtbl.replace atom_table "defaultLiteral" 2;
  next_id := 3

(* Normalization utilities *)

let negate_ineq (ineq : linIntExprWithRHS) : linIntExprWithRHS =
  {
    vars = List.map (fun (v, c) -> (v, -c)) ineq.vars;
    int  = -ineq.int;
  }

let rec normalize f =
  match f with
  | Not inner ->
      begin match normalize inner with
      | Not inner2 -> normalize inner2
      | simplified -> Not simplified
      end
  | And lst -> And (normalize_list lst)
  | Or lst -> Or (normalize_list lst)
  | Imply (a, b) -> Imply (normalize a, normalize b)
  | Z3ineq _ -> f
  | Z3var _ -> f
  | Z3eq _ -> f

and normalize_list lst =
  match lst with
  | Lnil -> Lnil
  | Lcons (x, xs) -> Lcons (normalize x, normalize_list xs)

let sort_linexpr (vars : (int * int) list) : (int * int) list =
  List.sort (fun (v1, _) (v2, _) -> compare v1 v2) vars
%}

%start start
%type <Types.item list> start

%left PLUS MINUS
%left TIMES

/* Tokens */
%token <char list> ATOM
%token TRUE FALSE NOT AND OR IMPLIES
%token TSEITIN ASSUMPTION RUP DELETE
%token LPAREN RPAREN LBRACK RBRACK COMMA
%token EQ GE GT LT LE TIMES
%token PLUS MINUS
%token <int> INT
%token EOF

%token FARKASP

%%

start:
  item_list EOF { $1 }

item_list:
  item { [$1] }
| item item_list { $1 :: $2 }

item:
  TSEITIN LPAREN formula_list RPAREN LBRACK RBRACK LBRACK formula_list RBRACK
    { Tseitin ($3, $8) }
| ASSUMPTION LBRACK RBRACK LBRACK formula_list RBRACK
    { Assumption $5 }
| RUP LBRACK RBRACK LBRACK formula_list RBRACK
    { Rup $5 }
| DELETE LBRACK RBRACK LBRACK formula_list RBRACK
    { Delete $5 }
| FARKASP LPAREN farkas_pairs RPAREN LBRACK RBRACK LBRACK formula_list RBRACK
    { FarkasP $3 }

formula_list:
  formula_list_nonempty { $1 }
|                       { Lnil }

formula_list_nonempty:
  formula {
    let simplified = normalize $1 in
    Lcons (simplified, Lnil)
  }
| formula COMMA formula_list_nonempty {
    let simplified = normalize $1 in
    Lcons (simplified, $3)
  }

formula:
  TRUE                        { Z3var 1 }
| FALSE                       { Z3var 0 }
| ATOM                        { Z3var (get_atom_id (string_of_char_list $1)) }
| NOT LPAREN formula RPAREN   { Not $3 }
| IMPLIES LPAREN formula COMMA formula RPAREN { Imply ($3, $5) }
| AND LPAREN formula_list_expr RPAREN { And $3 }
| OR LPAREN formula_list_expr RPAREN  { Or $3 }
| linexpr GE INT
    {
      Z3ineq {
        vars = sort_linexpr (List.rev $1);
        int  = $3
      }
    }

| linexpr LE INT
    {
      Z3ineq (
        negate_ineq {
          vars = sort_linexpr (List.rev $1);
          int  = $3
        }
      )
    }
| linexpr GT INT
    {
      Z3ineq {
        vars = sort_linexpr (List.rev $1);
        int  = $3 + 1
      }
    }

| linexpr LT INT
    {
      Z3ineq (
        negate_ineq {
          vars = sort_linexpr (List.rev $1);
          int  = $3 - 1
        }
      )
    }
| linexpr EQ INT
    {
      Z3eq {
        eq_vars = sort_linexpr (List.rev $1);
        eq_int  = $3
      }
    }


formula_list_expr:
  formula { Lcons ($1, Lnil) }
| formula COMMA formula_list_expr { Lcons ($1, $3) }

linexpr:
  linterm
    { [$1] }

| linexpr PLUS linterm
    { $3 :: $1 }

| linexpr MINUS linterm
    {
      let (v,c) = $3 in
      (v, -c) :: $1
    }

| linexpr PLUS LPAREN linexpr RPAREN
    { $4 @ $1 }

| linexpr MINUS LPAREN linexpr RPAREN
    { List.map (fun (v,c) -> (v,-c)) $4 @ $1 }

| LPAREN linexpr RPAREN
    { $2 }
;

linterm_list:
  linterm
    { [$1] }
| linterm COMMA linterm_list
    { $1 :: $3 }

linterm:
  ATOM
    { (get_atom_id (string_of_char_list $1), 1) }

| MINUS ATOM
    { (get_atom_id (string_of_char_list $2), -1) }

| INT TIMES ATOM
    { (get_atom_id (string_of_char_list $3), $1) }
    
farkas_pair:
  INT COMMA linexpr GE INT
    { ($1, { vars = $3; int = $5 }) }

| INT COMMA linexpr LE INT
    { ($1, negate_ineq { vars = $3; int = $5 }) }
      
| INT COMMA linexpr GT INT
    { ($1, { vars = $3; int = $5 + 1}) }

| INT COMMA linexpr LT INT
    { ($1, negate_ineq { vars = $3; int = $5 - 1 }) }
;

farkas_pairs:
  farkas_pair
    {
      let (m, c) = $1 in
      { mults = [m]; constrs = [c] }
    }

| farkas_pair COMMA farkas_pairs
    {
      let (m, c) = $1 in
      { mults = m :: $3.mults;
        constrs = c :: $3.constrs }
    }
;