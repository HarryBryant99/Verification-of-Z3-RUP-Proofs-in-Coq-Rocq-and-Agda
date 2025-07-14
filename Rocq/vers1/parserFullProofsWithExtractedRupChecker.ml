open RupProofChecker

exception SkipLine

(* Convert a char to your custom ascii type *)
let bool_of_bit c = if c = '1' then True else False

let ascii_of_char c =
 let code = Char.code c in
 let bits = List.init 8 (fun i -> bool_of_bit (if (code lsr (7 - i)) land 1 = 1 then '1' else '0')) in
 match bits with
 | [b0; b1; b2; b3; b4; b5; b6; b7] -> Ascii (b0, b1, b2, b3, b4, b5, b6, b7)
 | _ -> failwith "Invalid ASCII conversion"

(* Convert OCaml string to custom string type *)
let rec custom_string_of_string s =
 let len = String.length s in
 let rec aux i =
 if i >= len then EmptyString
 else String (ascii_of_char s.[i], aux (i + 1))
 in
 aux 0

(* Convert OCaml list to custom list type *)
let rec to_rup_list lst =
 match lst with
 | l when List.length l = 0 -> RupProofChecker.Nil
 | _ ->
 let hd = List.hd lst in
 let tl = List.tl lst in
 RupProofChecker.Cons (hd, to_rup_list tl)



(* Parse a literal from string *)
let parse_literal s : literal =
 let s = String.trim s in
 if String.length s >= 5 && String.sub s 0 4 = "Not(" && s.[String.length s - 1] = ')' then
 let inner = String.sub s 4 (String.length s - 5) in
 Neg (custom_string_of_string inner)
 else
 Pos (custom_string_of_string s)

let split_top_level_commas s =
 let len = String.length s in
 let rec aux i depth acc current =
 if i >= len then
 List.rev (String.concat "" (List.rev current) :: acc)
 else
 let c = s.[i] in
 match c with
 | '(' -> aux (i + 1) (depth + 1) acc (String.make 1 c :: current)
 | ')' -> aux (i + 1) (depth - 1) acc (String.make 1 c :: current)
 | ',' when depth = 0 ->
 aux (i + 1) depth (String.concat "" (List.rev current) :: acc) []
 | _ -> aux (i + 1) depth acc (String.make 1 c :: current)
 in
 aux 0 0 [] []

let parse_clause s : clause =
 let s = String.trim s in
 let inner = String.sub s 1 (String.length s - 2) in (* remove [ and ] *)
 let parts = split_top_level_commas inner in
 to_rup_list (List.map parse_literal parts)


 let parse_step line : proofStep =
  let line = String.trim line in
  if line = "" || line.[0] = '(' then raise SkipLine
  else
    try
      let space_idx = String.index line ' ' in
      let raw_kind = String.sub line 0 space_idx in
      let kind =
        try
          let paren_idx = String.index raw_kind '(' in
          String.sub raw_kind 0 paren_idx
        with Not_found -> raw_kind
      in

      (* Find all bracketed clauses *)
      let rec find_brackets acc i =
        try
          let start_idx = String.index_from line i '[' in
          let end_idx = String.index_from line start_idx ']' in
          let clause_str = String.sub line start_idx (end_idx - start_idx + 1) in
          find_brackets (clause_str :: acc) (end_idx + 1)
        with Not_found -> List.rev acc
      in

      let clauses = find_brackets [] space_idx in
      let clause =
        match clauses with
        | [] -> raise SkipLine
        | [c] -> parse_clause c
        | c1 :: c2 :: _ ->
            if String.trim c1 = "[]" then parse_clause c2 else parse_clause c1
      in

      match String.lowercase_ascii kind with
      | "tseitin" -> Tseitin' clause
      | "rup" -> Rup'0 clause
      | "assumption" -> Assumption' clause
      | "deletion" -> Deletion' clause
      | _ -> raise SkipLine
    with
    | Not_found | Invalid_argument _ -> raise SkipLine



 let parse_file filename : proofStep RupProofChecker.list =
  let chan = open_in filename in
  let file_content = really_input_string chan (in_channel_length chan) in
  close_in chan;

  let keywords = ["tseitin"; "rup"; "assumption"; "deletion"] in

  let is_step_start line =
    let trimmed = String.trim line in
    List.exists (fun kw -> String.length trimmed >= String.length kw &&
                           String.sub trimmed 0 (String.length kw) = kw)
                keywords
  in

  let lines = String.split_on_char '\n' file_content in

  let rec group acc current = function
    | [] ->
        List.rev (if current <> [] then String.concat " " (List.rev current) :: acc else acc)
    | line :: rest ->
        if is_step_start line then
          let acc = if current <> [] then String.concat " " (List.rev current) :: acc else acc in
          group acc [String.trim line] rest
        else
          group acc (String.trim line :: current) rest
  in

  let step_strings = group [] [] lines in

  let parsed_steps =
    let counter = ref 0 in
    List.fold_left (fun acc step_str ->
      try
        let step = parse_step step_str in
        incr counter;
        if !counter mod 10000 = 0 then
          Printf.printf "Parsed %d steps...\n%!" !counter;
        step :: acc
      with SkipLine -> acc
    ) [] step_strings
  in


  to_rup_list (List.rev parsed_steps)



let rec ocaml_list_of_rup_list = function
 | RupProofChecker.Nil -> []
 | RupProofChecker.Cons (x, xs) -> x :: ocaml_list_of_rup_list xs

(* Convert Coq ascii back to a character *)
let char_of_ascii (Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
 let bit_to_int = function
 | True -> 1
 | False -> 0
 in
 Char.chr (
 bit_to_int b7 +
 (bit_to_int b6 lsl 1) +
 (bit_to_int b5 lsl 2) +
 (bit_to_int b4 lsl 3) +
 (bit_to_int b3 lsl 4) +
 (bit_to_int b2 lsl 5) +
 (bit_to_int b1 lsl 6) +
 (bit_to_int b0 lsl 7)
 )

(* Convert Coq's string representation to an OCaml string *)
let rec string_of_string = function
 | EmptyString -> ""
 | String (c, s) -> Printf.sprintf "%c%s" (char_of_ascii c) (string_of_string s)

let string_of_literal = function
 | Pos s -> string_of_string s
 | Neg s -> "Not(" ^ string_of_string s ^ ")"

let string_of_clause clause =
 let literals = List.map string_of_literal (ocaml_list_of_rup_list clause) in
 "[" ^ String.concat ", " literals ^ "]"

let rec print_clauses clauses =
 match clauses with
 | RupProofChecker.Nil -> ()
 | RupProofChecker.Cons (clause, rest) ->
 print_endline (string_of_clause clause);
 print_clauses rest

let string_of_proofstep = function
 | Tseitin' clause -> "tseitin " ^ string_of_clause clause
 | Rup'0 clause -> "rup " ^ string_of_clause clause
 | Assumption' clause -> "assumption " ^ string_of_clause clause
 | Deletion' clause -> "deletion " ^ string_of_clause clause

 let rec string_of_preproof = function
 | RupProofChecker.Nil -> ""
 | RupProofChecker.Cons (step, rest) ->
 string_of_proofstep step ^ "\n" ^ string_of_preproof rest

(*
let proof = parse_file "test_p.txt"
let () = print_string (string_of_preproof proof)
*)

let () =
 if Array.length Sys.argv < 2 then
 print_endline "Usage: ./your_program "
 else
 let filename = Sys.argv.(1) in
 let proof = parse_file filename in
 let initial_formula = RupProofChecker.Nil in
 (*let p = print_string (string_of_preproof proof) in*)
 (* let p =  print_endline "Reading Complete." in *)
 let result = checkProof proof initial_formula in
 match result with
 | Pair (True, _) ->
 print_endline "Proof is valid."
 | Pair (False, Some step) ->
 print_endline "Proof is invalid. Failed at step:";
 print_endline (string_of_proofstep step)
 | Pair (False, None) ->
 print_endline "Proof is invalid, but no failing step was returned."
