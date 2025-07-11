
(* tseitincheck.ml *)

open Types

(* Helper functions *)

let rec equal_z3_formula f1 f2 =
  match f1, f2 with
  | Z3Var x, Z3Var y -> x = y
  | And l1, And l2
  | Or l1, Or l2
  | Imply l1, Imply l2 -> List.for_all2 equal_z3_formula l1 l2
  | Not f1', Not f2' -> equal_z3_formula f1' f2'
  | _, _ -> false

let equal_literal l1 l2 =
  match l1, l2 with
  | Pos f1, Pos f2 -> f1 = f2
  | Neg f1, Neg f2 -> f1 = f2
  | _, _ -> false

let neg f =
  match f with
  | Not inner -> inner
  | _ -> Not f

let not_child = function
  | Not f -> f
  | _ -> failwith "Expected Not"

let imp_child1 = function
  | Imply [a; _] -> a
  | _ -> failwith "Expected Imply with exactly two children"

let imp_child2 = function
  | Imply [_; b] -> b
  | _ -> failwith "Expected Imply with exactly two children"

let matches_imp = function
  | Imply [_; _] -> true
  | _ -> false

let matches_and (f : z3_formula) : bool =
  match f with
  | And _ -> true
  | _ -> false

let matches_or (f : z3_formula) : bool =
  match f with
  | Or _ -> true
  | _ -> false

let matches_not = function
  | Not _ -> true
  | _ -> false

let rec pos_to_z3 = function
  | PosZ3Var v -> Z3Var v
  | PosAnd l -> And l
  | PosOr l -> Or l
  | PosImply l -> Imply l

let z3_of_literal = function
  | Pos f -> pos_to_z3 f
  | Neg f -> Not (pos_to_z3 f)

let z3_of_literal_list (lits : clause) : z3_formula list =
  List.map z3_of_literal lits

let equal_clause (c1 : clause) (c2 : clause) : bool =
  List.length c1 = List.length c2 &&
  List.for_all2 equal_literal c1 c2

(* Helper to remove double negations *)
let rec strip_double_neg f =
  match f with
  | Not (Not inner) -> strip_double_neg inner
  | _ -> f

let equal_neg_list_formulas (forms : z3_formula list) (lits : clause) : bool =
  let negated_forms = List.map neg forms in
  let z3_lits = List.map z3_of_literal lits in
  List.length negated_forms = List.length z3_lits &&
  List.for_all2 equal_z3_formula negated_forms z3_lits

let equal_list_formulas (forms : z3_formula list) (lits : clause) : bool =
  let z3_lits = List.map z3_of_literal lits in
  List.length forms = List.length z3_lits &&
  List.for_all2 equal_z3_formula forms z3_lits

let and_child_list (lit : literal) : z3_formula list =
  match lit with
  | Pos (PosAnd lst) -> lst
  | Neg (PosAnd lst) -> lst
  | _ -> failwith "Expected a PosOrNeg(PosAnd [...])"

let or_child_list (lit : literal) : z3_formula list =
  match lit with
  | Pos (PosOr lst) -> lst
  | Neg (PosOr lst) -> lst
  | _ -> failwith "Expected a PosOrNeg(PosOr [...])"

(* Helper: convert z3_formula to pos_z3_formula if possible *)
let rec to_pos_z3_formula (f : z3_formula) : pos_z3_formula option =
  match f with
  | Z3Var v -> Some (PosZ3Var v)
  | And lst -> Some (PosAnd lst)
  | Or lst -> Some (PosOr lst)
  | Imply lst -> Some (PosImply lst)
  | Not _ -> None  (* Not is not allowed in pos_z3_formula *)

let string_of_z3_variable (v : z3_variable) : string =
  String.concat "" (List.map (String.make 1) v)

let rec string_of_z3_formula (f : z3_formula) : string =
  match f with
  | Z3Var v -> string_of_z3_variable v
  | And lst -> 
      "And(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Or lst -> 
      "Or(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Imply lst -> 
      "Imply(" ^ String.concat ", " (List.map string_of_z3_formula lst) ^ ")"
  | Not f' -> 
      "Not(" ^ string_of_z3_formula f' ^ ")"

let rec strip_all_double_neg (f : z3_formula) : z3_formula =
  match f with
  | Not (Not inner) -> strip_all_double_neg inner
  | _ -> f

(*Case 1:*)
let impelim (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "impElim \n";*)
  let f0 = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  let f2 = strip_all_double_neg (z3_of_literal (List.nth f_list 2)) in
  let g0 = strip_all_double_neg (z3_of_literal (List.nth g_list 0)) in
  let g1 = strip_all_double_neg (z3_of_literal (List.nth g_list 1)) in
  let g2 = strip_all_double_neg (z3_of_literal (List.nth g_list 2)) in
  let a = strip_all_double_neg (imp_child1 (not_child f0)) in
  let b = strip_all_double_neg (imp_child2 (not_child f0)) in

  equal_z3_formula f1 (neg a) &&
  equal_z3_formula f2 b &&
  equal_z3_formula g0 f1 &&
  equal_z3_formula g1 f2 &&
  equal_z3_formula g2 f0

(*Case 2:*)
let impintro (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "impintro \n";*)
  let f0 = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  let g0 = strip_all_double_neg (z3_of_literal (List.nth g_list 0)) in
  let g1 = strip_all_double_neg (z3_of_literal (List.nth g_list 1)) in
  let a = strip_all_double_neg (imp_child1 f1) in
  (*let b = imp_child2 f1 in*)
  equal_z3_formula f0 a &&
  equal_z3_formula g0 f0 &&
  equal_z3_formula g1 f1

(*Case 3:*)
let impintro2 (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "impintro2 \n";*)
  let f0 = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  let g0 = strip_all_double_neg (z3_of_literal (List.nth g_list 0)) in
  let g1 = strip_all_double_neg (z3_of_literal (List.nth g_list 1)) in
  (*let a = imp_child1 f1 in*)
  let b = strip_all_double_neg (imp_child2 f1) in
  equal_z3_formula f0 (neg b) &&
  equal_z3_formula g0 f0 &&
  equal_z3_formula g1 f1

(*Case 4:*)
let not_case (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "not \n";*)
  let b = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  let g0 = strip_all_double_neg (z3_of_literal (List.nth g_list 0)) in
  let g1 = strip_all_double_neg (z3_of_literal (List.nth g_list 1)) in  
  equal_z3_formula f1 (neg b) &&
  equal_z3_formula g0 b &&
  equal_z3_formula g1 (neg b)

(*Case 5:*)
let andelim (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "andElim \n";*)
  let f0 = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  match not_child f0 with
  | And aList ->
      let rec find_match lst idx =
        match lst with
        | [] -> false
        | hd :: tl ->
            if equal_z3_formula hd f1 then
              true
            else
              find_match tl (idx + 1)
      in
      find_match aList 0
  | _ -> false

(*Case 6:*)
let andintro (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "andIntro \n";*)
  let len = List.length f_list in
  if len < 2 then false
  else
    let last = List.nth f_list (len - 1) in
    let rest = List.init (len - 1) (fun i -> List.nth f_list i) in
    if equal_clause f_list g_list then
      let and_children = and_child_list last in
      equal_neg_list_formulas and_children rest
    else
      false

(*Case 7:*)
let orintro (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "orIntro \n";*)
  let f0 = strip_all_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_double_neg (z3_of_literal (List.nth f_list 1)) in
  match f1 with
  | Or aList ->
      let rec find_match lst idx =
        match lst with
        | [] -> false
        | hd :: tl ->
            if equal_z3_formula (neg hd) f0 then
              true
            else
              find_match tl (idx + 1)
      in
      find_match aList 0
  | _ -> false

(*Case 8:*)
let orelim (f_list : clause) (g_list : clause) : bool =
  (*Format.printf "orElim \n";*)
  let len = List.length f_list in
  if len < 2 then false
  else
    let last = List.nth f_list (len - 1) in
    let rest = List.init (len - 1) (fun i -> List.nth f_list i) in
    if equal_clause f_list g_list then
      let or_children = or_child_list last in
      equal_list_formulas or_children rest
    else
      false

(* Main Tseitin checker *)
let tseitin_checker (f_list : clause) (g_list : clause) : bool =
  let len_f = List.length f_list in
  let len_g = List.length g_list in

  (* Case 6: tseitinAndIntro *)
  if len_f >= 2 then
    let last = z3_of_literal (List.nth f_list (len_f - 1)) in
    (*let rest = z3_of_literal_list (List.init (len_f - 1) (List.nth f_list)) in*)
    if matches_and last then
      andintro f_list g_list
    else if matches_not last && 
      matches_or (not_child last) 
      then
      orelim f_list g_list
    else 
      (* Case 1: tseitinImpElim *)
      if len_f = 3 && len_g = 3 then
      match List.nth f_list 0 with
      | Neg (PosImply [a; b]) ->
          let z3_imp = Imply [a; b] in
          if matches_not (Not z3_imp) && matches_imp z3_imp then
            impelim f_list g_list
          else ( 
            Format.printf "Error Case 0\n";
            false
            )
      | _ -> ( 
            Format.printf "Error Case 1\n";
            false
            )

      (* Case 2–5: 2-element clauses *)
      else if len_f = 2 && len_g = 2 then
        let f0 = z3_of_literal (List.nth f_list 0) in
        let f1 = z3_of_literal (List.nth f_list 1) in
        let g0 = z3_of_literal (List.nth g_list 0) in
        let g1 = z3_of_literal (List.nth g_list 1) in

        match f1 with
        | Imply [a; b] ->
            if equal_z3_formula f0 a then
              impintro f_list g_list
            else if equal_z3_formula f0 (neg b) then
              impintro2 f_list g_list
            else
              ( 
            Format.printf "Error Case 2\n";
            false
            )
        | Or _ ->
            if
              equal_z3_formula f0 g0 &&
              equal_z3_formula f1 g1
              then
              orintro f_list g_list
            else
              ( 
            Format.printf "Error Case 3\n";
            false
            )
        | Not a ->
            if matches_not f0 &&
              matches_and (not_child f0) &&
              equal_z3_formula f0 g1 &&
              equal_z3_formula f1 g0
              then
              andelim f_list g_list
            else
              not_case f_list g_list
        | _ ->
            if matches_not f0 &&
              matches_and (not_child f0) &&
              equal_z3_formula f0 g1 &&
              equal_z3_formula f1 g0
              then
              andelim f_list g_list
            else
              not_case f_list g_list
      else ( 
            Format.printf "Error Case 4\n";
            false
            )
  else ( 
            Format.printf "Error Case 5\n";
            false
            )
(*
let tseitin_checker (f_list : clause) (g_list : clause) : bool =
  match List.length f_list, List.length g_list with
  | 3, 3 -> (
      match List.nth f_list 0 with
      | Neg (PosImply [a; b]) ->
          let z3_imp = Imply [a; b] in
          if matches_not (Not z3_imp) && matches_imp z3_imp then
            impelim f_list g_list
          else false
      | _ -> false
    )
  | 2, 2 -> (
    match z3_of_literal (List.nth f_list 1) with
    | Imply [a; b] ->
        let f0 = z3_of_literal (List.nth f_list 0) in
        if equal_z3_formula f0 a then
          impintro f_list g_list
        else
          impintro2 f_list g_list
    | Not a -> 
        let f0 = z3_of_literal (List.nth f_list 0) in
        let f1 = z3_of_literal (List.nth f_list 1) in
        let g0 = z3_of_literal (List.nth g_list 0) in
        let g1 = z3_of_literal (List.nth g_list 1) in
        if matches_not f0 &&
        (match not_child f0 with And _ -> true | _ -> false) &&
          equal_z3_formula f0 g1 &&
          equal_z3_formula f1 g0
        then (
          andelim f_list g_list
        )
        else
          not_case f_list g_list
    | _ ->
        let f0 = z3_of_literal (List.nth f_list 0) in
        let f1 = z3_of_literal (List.nth f_list 1) in
        let g0 = z3_of_literal (List.nth g_list 0) in
        let g1 = z3_of_literal (List.nth g_list 1) in
        if matches_not f0 &&
        (match not_child f0 with And _ -> true | _ -> false) &&
          equal_z3_formula f0 g1 &&
          equal_z3_formula f1 g0
        then (
          andelim f_list g_list
        )
        else
          not_case f_list g_list
  )
  | _ -> false
*)