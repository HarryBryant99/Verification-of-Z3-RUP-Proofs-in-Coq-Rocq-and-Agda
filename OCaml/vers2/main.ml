open Parser
open Lexer
open Step_converter
open Proven_sat_checker
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

let string_of_z3_variable (v : z3_Variable) : string =
  String.concat "" (List.map (String.make 1) v)

let rec string_of_z3_formula (f : z3_Formula) : string =
  match f with
  | Z3var v -> string_of_z3_variable v
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
  | Pos (Pos_z3var v) -> (implode v)
  | Pos (Pos_and lst) -> "And(" ^ string_of_list_z3_formula lst ^ ")"
  | Pos (Pos_or lst) -> "Or(" ^ string_of_list_z3_formula lst ^ ")"
  | Pos (Pos_imply (a,b)) -> "Implies(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | Neg (Pos_z3var v) -> "Not(" ^ (implode v) ^ ")"
  | Neg (Pos_and lst) -> "Not(And(" ^ string_of_list_z3_formula lst ^ "))"
  | Neg (Pos_or lst) -> "Not(Or(" ^ string_of_list_z3_formula lst ^ "))"
  | Neg (Pos_imply (a,b)) -> "Not(Implies(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ "))"

let string_of_clause clause =
  "[" ^ String.concat ", " (List.map string_of_literal clause) ^ "]"

let rec string_of_nat (n : nat) : string =
  match n with
  | O -> "0"
  | S n' -> string_of_int (1 + int_of_nat n')

and int_of_nat (n : nat) : int =
  match n with
  | O -> 0
  | S n' -> 1 + int_of_nat n'

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
      "TseitinAndElim((" ^ string_of_list_z3_formula lst ^ "), " ^ string_of_nat i ^ ")"
  | TseitinOrIntro (lst, i) ->
      "TseitinOrIntro((" ^ string_of_list_z3_formula lst ^ "), " ^ string_of_nat i ^ ")"
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
(*      
  | Deletion c ->
      Printf.printf "Deletion: %s\n" (string_of_clause c)
*)

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
    Printf.printf "Parsing Complete\n";

    let itemsRev = List.rev items in

    Printf.printf "Reversing Complete\n";


    let items_prime = process_items itemsRev in


    Printf.printf "Processing Complete\n";
    (*print_items items_prime;*)
    Printf.printf "Starting Checking\n";
  
(*   
    let result = zProofCheck items_prime in
    if result then
      Printf.printf "Proof check passed.\n"
    else begin
      Printf.printf "Proof check failed.\n";
      (*(match failing_step with
       | Some step -> print_item step
       | None -> ());
      exit 1
      *)
    end
*)

match zProofCheckWithFailure items_prime with
| Passed ->
    Printf.printf "Proof check passed.\n"
| Failed step ->
    Printf.printf "Proof check failed at step:\n";
    print_item step;
    Printf.printf "\n%s\n" (string_of_list_z3_formula (zProofItem2ConclusionOpt step));
    exit 1
