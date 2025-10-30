open Types
open Parser
open Lexer

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

let rec string_of_z3_formula = function
  | Z3Var v -> "Z3F: " ^ v
  | Not f -> "Z3F: Not(" ^ string_of_z3_formula f ^ ")"
  | Imply lst -> "Z3F: Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | And lst -> "Z3F: And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Or lst -> "Z3F: Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"

let string_of_literal = function
  | Pos (PosZ3Var v) -> "L: " ^ v
  | Pos (PosAnd lst) -> "L: And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (PosOr lst) -> "L: Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Pos (PosImply lst) -> "L: Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Neg (PosZ3Var v) -> "Not(L: " ^ v ^ ")"
  | Neg (PosAnd lst) -> "Not(L: And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (PosOr lst) -> "Not(L: Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"
  | Neg (PosImply lst) -> "Not(L: Implies(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ "))"

let string_of_clause clause =
  "[" ^ String.concat ", " (List.map string_of_literal clause) ^ "]"

let print_item = function
  | Tseitin (c1, c2) ->
      Printf.printf "Tseitin: %s %s\n" (string_of_clause c1) (string_of_clause c2)
  | Assumption c ->
      Printf.printf "Assumption: %s\n" (string_of_clause c)
  | Rup c ->
      Printf.printf "Rup: %s\n" (string_of_clause c)

let () =
  if Array.length Sys.argv < 2 then
    Printf.printf "Usage: %s <input_file>\n" Sys.argv.(0)
  else
    let items = parse_file Sys.argv.(1) in
    List.iter print_item items
