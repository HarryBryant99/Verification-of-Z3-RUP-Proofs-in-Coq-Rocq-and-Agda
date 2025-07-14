open Types
open Parser
open Lexer
open Tseitincheck
open Rupchecker_z3_datatype

let implode cl =
  let buf = Buffer.create (List.length cl) in
  List.iter (Buffer.add_char buf) cl;
  Buffer.contents buf

let parse_from_char_list (chars : char list) : Rupchecker_z3_datatype.proofStep list =
  let str = String.of_seq (List.to_seq chars) in
  let lexbuf = Lexing.from_string str in
  try
    Parser.start Lexer.token lexbuf
  with
  | End_of_file -> failwith "Unexpected end of input"
  | Parsing.Parse_error -> failwith "Parse error"

let rec string_of_z3_formula = function
  | Z3var v -> (implode v)
  | Not f -> "Not(" ^ string_of_z3_formula f ^ ")"
  | Imply lst -> "Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | And lst -> "And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Or lst -> "Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"

let string_of_literal = function
  | Pos (Pos_z3var v) -> (implode v)
  | Pos (Pos_and lst) -> "And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (Pos_or lst) -> "Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (Pos_imply lst) -> "Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Neg (Pos_z3var v) -> "Not(" ^ (implode v) ^ ")"
  | Neg (Pos_and lst) -> "Not(And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (Pos_or lst) -> "Not(Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (Pos_imply lst) -> "Not(Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"

let string_of_clause clause =
  "[" ^ String.concat ", " (List.map string_of_literal clause) ^ "]"

let print_item = function
  | Tseitin (c1, c2) ->
      Printf.printf "Tseitin: %s %s\n" (string_of_clause c1) (string_of_clause c2)
  | Assumption c ->
      Printf.printf "Assumption: %s\n" (string_of_clause c)
  | Rup c ->
      Printf.printf "Rup: %s\n" (string_of_clause c)
  | Deletion c ->
      Printf.printf "Deletion: %s\n" (string_of_clause c)

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

let rec checkProof p f =
  match p with
  | [] -> (true, None)
  | step :: ps ->
    match step with
    | Tseitin (f_clause, g_clause) ->
        if tseitin_checker f_clause g_clause then
          checkProof ps (app f [g_clause])
        else
          (false, Some step)
    | Rup c ->
        if rUP_Checker f c then
          checkProof ps (app f [c])
        else
          (false, Some step)
    | Assumption a ->
        checkProof ps (app f [a])
    | Deletion c ->
        checkProof ps (remove_clause c f)

let () =
  if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s <input_file>\n" Sys.argv.(0)
  else
    let items = parse_file Sys.argv.(1) in
    let (result, failing_step) = checkProof items [] in
    if result then
      Printf.printf "Proof check passed.\n"
    else begin
      Printf.printf "Proof check failed at step:\n";
      (match failing_step with
       | Some step -> print_item step
       | None -> ());
      exit 1
    end


