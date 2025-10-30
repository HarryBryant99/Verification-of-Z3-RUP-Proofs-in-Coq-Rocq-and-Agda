open Types
open Parser
open Lexer
open Tseitincheck

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

let rec string_of_z3_formula = function
  | Z3Var v -> (implode v)
  | Not f -> "Not(" ^ string_of_z3_formula f ^ ")"
  | Imply lst -> "Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | And lst -> "And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Or lst -> "Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"

let string_of_literal = function
  | Pos (PosZ3Var v) -> (implode v)
  | Pos (PosAnd lst) -> "And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (PosOr lst) -> "Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (PosImply lst) -> "Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Neg (PosZ3Var v) -> "Not(" ^ (implode v) ^ ")"
  | Neg (PosAnd lst) -> "Not(And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (PosOr lst) -> "Not(Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (PosImply lst) -> "Not(Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"

let string_of_clause clause =
  "[" ^ String.concat ", " (List.map string_of_literal clause) ^ "]"

let print_item = function
  | Tseitin (c1, c2) ->
      Printf.printf "Tseitin: %s %s\n" (string_of_clause c1) (string_of_clause c2)
  | Assumption c ->
      Printf.printf "Assumption: %s\n" (string_of_clause c)
  | Rup c ->
      Printf.printf "Rup: %s\n" (string_of_clause c)

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

let () =
  if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s <input_file>\n" Sys.argv.(0)
  else
    let items = parse_file Sys.argv.(1) in
    let all_valid = ref true in
    List.iter (function
      | Tseitin (f_clause, g_clause) as item ->
          if not (tseitin_checker f_clause g_clause) then begin
            Printf.printf "Tseitin check failed for item:\n";
            print_item item;
            all_valid := false
          end
      | _ -> ()
    ) items;
    if !all_valid then
      Printf.printf "All Tseitin checks passed: true\n"
    else begin
      Printf.printf "All Tseitin checks passed: false\n";
      exit 1
    end

