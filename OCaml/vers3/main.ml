open Parser
open Lexer
open Step_converter
open Proven_checker_farkas_6
open Types

let implode cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

let parse_from_char_list (chars : char list) : Types.item list =
  let str = String.of_seq (List.to_seq chars) in
  let lexbuf = Lexing.from_string str in
  try
    Parser.start Lexer.token lexbuf
  with
  | End_of_file -> failwith "Unexpected end of input"
  | Parsing.Parse_error -> failwith "Parse error"

let string_of_z3_variable (v : z3_Variable_Bool) : string =
  "b" ^ string_of_int v

let string_of_z3_int_variable (v : z3_Variable_Int) : string =
  "i" ^ string_of_int v

let string_of_linterm (v, coeff : z3_Variable_Int * int) =
  if coeff = 1 then
    string_of_z3_int_variable v
  else if coeff = -1 then
    "-" ^ string_of_z3_int_variable v
  (*else if coeff < -1 then
    "-" ^ string_of_int coeff ^ "*" ^ string_of_z3_int_variable v*)
  else
    string_of_int coeff ^ "*" ^ string_of_z3_int_variable v

let string_of_linexpr (vars : linIntExpr) : string =
  match vars with
  | [] -> "0"
  | (v, c) :: rest ->
      let first = string_of_linterm (v, c) in
      let tail =
        List.map
          (fun (v, c) ->
             if c >= 0 then
               " + " ^ string_of_linterm (v, c)
             else
               " - " ^ string_of_linterm (v, -c))
          rest
      in
      first ^ String.concat "" tail

let string_of_ineq (ineq : linIntExprWithRHS) : string =
  string_of_linexpr ineq.vars ^ " >= " ^ string_of_int ineq.int

let string_of_eq eq =
  string_of_linexpr eq.eq_vars ^ " == " ^ string_of_int eq.eq_int

let string_of_int_list lst =
  "[" ^ String.concat ", " (List.map string_of_int lst) ^ "]"

let string_of_listIntExpr (lhs : listIntExpr) : string =
  lhs
  |> List.map (fun (v, coeffs) ->
         string_of_z3_int_variable v ^ " -> " ^ string_of_int_list coeffs)
  |> String.concat ", "

let string_of_farkas_formulas (f : farkasFormulas) : string =
  let lhs_str = string_of_listIntExpr f.lhs in
  let rhs_str = string_of_int_list f.rhs in
  "{ lhs = " ^ lhs_str ^ "; rhs = " ^ rhs_str ^ " }"

let string_of_farkas_step (step : farkasStep) : string =
  "FarkasStep {\n" ^
  "  mults = " ^ string_of_int_list step.mults ^ ";\n" ^
  "  constrs = " ^ string_of_farkas_formulas step.constrs ^ "\n" ^
  "}"

let rec string_of_z3_formula (f : z3_Formula) : string =
  match f with
  | Z3var v -> string_of_z3_variable v
  | Z3ineq ineq -> string_of_ineq ineq
  | Z3eq eq -> string_of_eq eq
  | And lst -> "And(" ^ string_of_list_z3_formula lst ^ ")"
  | Or lst -> "Or(" ^ string_of_list_z3_formula lst ^ ")"
  | Imply (a, b) -> "Imply(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | Not f' -> "Not(" ^ string_of_z3_formula f' ^ ")"

and string_of_list_z3_formula (lst : listZ3_Formula) : string =
  match lst with
  | Lnil -> "[]"
  | Lcons (h, Lnil) -> string_of_z3_formula h
  | Lcons (h, t) -> string_of_z3_formula h ^ ", " ^ string_of_list_z3_formula t

let string_of_literal = function
  | Pos (Pos_z3var v) -> string_of_z3_variable v
  | Pos (Pos_z3ineq ineq) -> string_of_ineq ineq
  | Pos (Pos_z3eq eq) -> string_of_eq eq
  | Pos (Pos_and lst) -> "And(" ^ string_of_list_z3_formula lst ^ ")"
  | Pos (Pos_or lst) -> "Or(" ^ string_of_list_z3_formula lst ^ ")"
  | Pos (Pos_imply (a,b)) -> "Implies(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | Neg (Pos_z3var v) -> "Not(" ^ string_of_z3_variable v ^ ")"
  | Neg (Pos_z3ineq ineq) -> "Not(" ^ string_of_ineq ineq ^ ")"
  | Neg (Pos_z3eq eq) -> "Not(" ^ string_of_eq eq ^ ")"
  | Neg (Pos_and lst) -> "Not(And(" ^ string_of_list_z3_formula lst ^ "))"
  | Neg (Pos_or lst) -> "Not(Or(" ^ string_of_list_z3_formula lst ^ "))"
  | Neg (Pos_imply (a,b)) -> "Not(Implies(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ "))"

let string_of_clause clause =
  "[" ^ String.concat ", " (List.map string_of_literal clause) ^ "]"

let rec string_of_tseitin_step (step : tseitinStep) : string =
  match step with
  | TseitinNot f ->
      "TseitinNot(" ^ string_of_z3_formula f ^ ")"
  | TseitinImpElim (a, b) ->
      "TseitinImpElim(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | TseitinImpIntro1 (a, b) ->
      "TseitinImpIntro1(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | TseitinImpIntro2 (a, b) ->
      "TseitinImpIntro2(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | TseitinImpIntro3 (a, b) ->
      "TseitinImpIntro3(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | TseitinAndIntro lst ->
      "TseitinAndIntro(" ^ string_of_list_z3_formula lst ^ ")"
  | TseitinAndElim (lst, i) ->
      "TseitinAndElim((" ^ string_of_list_z3_formula lst ^ "), " ^ (string_of_int i) ^ ")"
  | TseitinOrIntro (lst, i) ->
      "TseitinOrIntro((" ^ string_of_list_z3_formula lst ^ "), " ^ (string_of_int i) ^ ")"
  | TseitinOrElim lst ->
      "TseitinOrElim(" ^ string_of_list_z3_formula lst ^ ")"

let print_item = function
  | TseitinStep c ->
      Printf.printf "Tseitin: %s \n" (string_of_tseitin_step c)
  | TseitinStepRed (c1, c2) ->
      Printf.printf "Tseitin (Reduced): %s, (%s)\n" (string_of_tseitin_step c1) (string_of_list_z3_formula c2)
  | AssumptionZ3 c ->
      Printf.printf "Assumption: %s\n" (string_of_list_z3_formula c)
  | RupZ3proof c ->
      Printf.printf "Rup: %s\n" (string_of_list_z3_formula c)      
  | Deletion c ->
      Printf.printf "Deletion: %s\n" (string_of_list_z3_formula c)
  | Farkas c ->
      Printf.printf "Farkas: %s\n" (string_of_farkas_step c)

let parse_file filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  try
    let result = Parser.start Lexer.token lexbuf in
    close_in chan;
    result
  with
  | End_of_file ->
      close_in chan;
      failwith "Unexpected end of file"
  | Parsing.Parse_error ->
      close_in chan;
      failwith "Parse error"

let print_items (items : zProofItem list) : unit =
  List.iter print_item items

let () =
  if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s <input_file>\n" Sys.argv.(0)
  else
    (*let items = parse_file Sys.argv.(1) in*)
    let items = parse_file Sys.argv.(1) in
    let length_p = (List.length items) in 
    Printf.printf "Parsing Complete: %d steps parsed\n" length_p;

    let itemsRev = List.rev items in

    Printf.printf "Reversing Complete\n";


    let items_prime = process_items itemsRev in


    Printf.printf "Processing Complete\n";

    (*
    print_items items_prime;
    *)

    Printf.printf "Starting Checking\n";
    flush stdout;
  let ((a, c), result) = checkList [] [] items_prime true in
  if result then
    Printf.printf "Proof check passed.\n"
  else
    Printf.printf "Proof check failed.\n"