
(* tseitincheck.ml *)

open Rupchecker

(* Helper functions *)

let rec equal_z3_formula f1 f2 =
  match f1, f2 with
  | Z3var x, Z3var y -> x = y
  | And l1, And l2
  | Or l1, Or l2 -> equal_list_z3_formula l1 l2
  | Imply (a1, b1), Imply (a2, b2) -> equal_z3_formula a1 a2 && equal_z3_formula b1 b2
  | Not f1', Not f2' -> equal_z3_formula f1' f2'
  | _, _ -> false

and equal_list_z3_formula l1 l2 =
  match l1, l2 with
  | Lnil, Lnil -> true
  | Lcons (h1, t1), Lcons (h2, t2) ->
      equal_z3_formula h1 h2 && equal_list_z3_formula t1 t2
  | _, _ -> false

let rec compare_z3_formula f1 f2 =
  match f1, f2 with
  | Z3var x, Z3var y -> compare x y
  | Not a, Not b -> compare_z3_formula a b
  | And l1, And l2 -> compare_list_z3_formula l1 l2
  | Or l1, Or l2 -> compare_list_z3_formula l1 l2
  | Imply (a1, b1), Imply (a2, b2) ->
      let cmp_a = compare_z3_formula a1 a2 in
      if cmp_a <> 0 then cmp_a else compare_z3_formula b1 b2
  | Z3var _, _ -> -1
  | _, Z3var _ -> 1
  | Not _, _ -> -1
  | _, Not _ -> 1
  | And _, _ -> -1
  | _, And _ -> 1
  | Or _, _ -> -1
  | _, Or _ -> 1
and compare_list_z3_formula l1 l2 =
  match l1, l2 with
  | Lnil, Lnil -> 0
  | Lnil, _ -> -1
  | _, Lnil -> 1
  | Lcons (h1, t1), Lcons (h2, t2) ->
      let cmp_h = compare_z3_formula h1 h2 in
      if cmp_h <> 0 then cmp_h else compare_list_z3_formula t1 t2

let rec compare_pos_z3_formula p1 p2 =
  match p1, p2 with
  | Pos_z3var v1, Pos_z3var v2 -> compare v1 v2
  | Pos_and l1, Pos_and l2 -> compare_list_z3_formula l1 l2
  | Pos_or l1, Pos_or l2 -> compare_list_z3_formula l1 l2
  | Pos_imply (a1, b1), Pos_imply (a2, b2) ->
      let cmp_a = compare_z3_formula a1 a2 in
      if cmp_a <> 0 then cmp_a else compare_z3_formula b1 b2
  | Pos_z3var _, _ -> -1
  | _, Pos_z3var _ -> 1
  | Pos_and _, _ -> -1
  | _, Pos_and _ -> 1
  | Pos_or _, _ -> -1
  | _, Pos_or _ -> 1


let compare_literal l1 l2 =
  match l1, l2 with
  | Pos p1, Pos p2
  | Neg p1, Neg p2 -> compare_pos_z3_formula p1 p2
  | Pos _, Neg _ -> -1
  | Neg _, Pos _ -> 1

  
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
  | Imply (a, _) -> a
  | _ -> failwith "Expected Imply with exactly two children"

let imp_child2 = function
  | Imply (_, b) -> b
  | _ -> failwith "Expected Imply with exactly two children"

let matches_imp = function
  | Imply (_, _) -> true
  | _ -> false

let matches_and (f : z3_Formula) : bool =
  match f with
  | And _ -> true
  | _ -> false

let matches_or (f : z3_Formula) : bool =
  match f with
  | Or _ -> true
  | _ -> false

let matches_not = function
  | Not _ -> true
  | _ -> false

let rec pos_to_z3 = function
  | Pos_z3var v -> Z3var v
  | Pos_and l -> And l
  | Pos_or l -> Or l
  | Pos_imply (a, b) -> Imply (a, b)

let z3_of_literal = function
  | Pos f -> pos_to_z3 f
  | Neg f -> Not (pos_to_z3 f)

let z3_of_literal_list (lits : clause) : z3_Formula list =
  List.map z3_of_literal lits

let equal_clause (c1 : clause) (c2 : clause) : bool =
  List.length c1 = List.length c2 &&
  List.for_all2 equal_literal c1 c2

(* Helper: convert z3_formula to pos_z3_formula if possible *)
let rec to_pos_z3_formula (f : z3_Formula) : pos_Z3_Formula option =
  match f with
  | Z3var v -> Some (Pos_z3var v)
  | And lst -> Some (Pos_and lst)
  | Or lst -> Some (Pos_or lst)
  | Imply (a, b) -> Some (Pos_imply (a, b))
  | Not _ -> None  (* Not is not allowed in pos_z3_formula *)

let string_of_z3_variable (v : z3_Variable) : string =
  String.concat "" (List.map (String.make 1) v)

let rec string_of_z3_formula (f : z3_Formula) : string =
  match f with
  | Z3var v -> string_of_z3_variable v
  | And lst -> "And(" ^ string_of_list_z3_formula lst ^ ")"
  | Or lst -> "Or(" ^ string_of_list_z3_formula lst ^ ")"
  | Imply (a, b) -> "Imply(" ^ string_of_z3_formula a ^ ", " ^ string_of_z3_formula b ^ ")"
  | Not f' -> "Not(" ^ string_of_z3_formula f' ^ ")"

and string_of_list_z3_formula lst =
  match lst with
  | Lnil -> ""
  | Lcons (h, Lnil) -> string_of_z3_formula h
  | Lcons (h, t) -> string_of_z3_formula h ^ ", " ^ string_of_list_z3_formula t

let print_clause clause =
  let sorted = clause in
  Printf.printf "[%s]\n"
    (String.concat "; " (List.map string_of_z3_formula sorted))

let equal_neg_list_formulas (forms : z3_Formula list) (lits : clause) : bool =
  let negated_forms = List.map neg forms in
  let z3_lits = List.map z3_of_literal lits in
  List.length negated_forms = List.length z3_lits &&
  List.for_all2 equal_z3_formula negated_forms z3_lits


let equal_list_formulas (forms : z3_Formula list) (lits : clause) : bool =
  let z3_lits = List.map z3_of_literal lits in
  List.length forms = List.length z3_lits &&
  List.for_all2 equal_z3_formula forms z3_lits

let rec list_z3_formula_to_list (lst : listZ3_Formula) : z3_Formula list =
  match lst with
  | Lnil -> []
  | Lcons (h, t) -> h :: list_z3_formula_to_list t

let and_child_list (lit : literal) : z3_Formula list =
  match lit with
  | Pos (Pos_and lst)
  | Neg (Pos_and lst) -> list_z3_formula_to_list lst
  | _ -> failwith "Expected a PosOrNeg(PosAnd [...])"

let or_child_list (lit : literal) : z3_Formula list =
  match lit with
  | Pos (Pos_or lst)
  | Neg (Pos_or lst) -> list_z3_formula_to_list lst
  | _ -> failwith "Expected a PosOrNeg(PosOr [...])"

let rec strip_all_outer_double_neg (f : z3_Formula) : z3_Formula =
  match f with
  | Not (Not inner) -> strip_all_outer_double_neg inner
  | _ -> f


(* Assumes: literal_eqb and negate_literal are already defined *)

(* Check if a clause is a singleton containing just ¬e *)
let clause_is_negation_of_literal e clause =
  match clause with
  | [lit] -> literal_eqb lit (negate e)
  | _ -> false

(* Main function *)
let check_negated_difference_singletons f g clauses =
  let difference =
    List.filter (fun lit_f ->
      not (List.exists (fun lit_g -> literal_eqb lit_f lit_g) g)
    ) f
  in
  List.for_all
    (fun lit ->
      List.exists (clause_is_negation_of_literal lit) clauses
    ) difference

(*Case 1:*)
let impelim (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  (*Format.printf "impElim \n";*)
  let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
  let f2 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 2)) in
  let a = strip_all_outer_double_neg (imp_child1 (not_child f0)) in
  let b = strip_all_outer_double_neg (imp_child2 (not_child f0)) in
  
  if equalListLength then
    let g0 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 0)) in
    let g1 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 1)) in
    let g2 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 2)) in
    (
    equal_z3_formula f1 (neg a) &&
    equal_z3_formula f2 b &&
    equal_z3_formula g0 f1 &&
    equal_z3_formula g1 f2 &&
    equal_z3_formula g2 f0
    ) 
  
  else
    (
    equal_z3_formula f1 (neg a) &&
    equal_z3_formula f2 b &&
    check_negated_difference_singletons f_list g_list ass
    ) 

(*Case 2:*)
let impintro (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  (*Format.printf "impintro \n";*)

  let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
  let a = strip_all_outer_double_neg (imp_child1 f1) in

  if equalListLength then
    let g0 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 0)) in
    let g1 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 1)) in
    equal_z3_formula f0 a &&
    equal_z3_formula g0 f0 &&
    equal_z3_formula g1 f1
  
  else
    equal_z3_formula f0 a &&
    check_negated_difference_singletons f_list g_list ass

(*Case 3:*)
let impintro2 (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  (*Format.printf "impintro2 \n";*)

  let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
  let b = strip_all_outer_double_neg (imp_child2 f1) in

  if equalListLength then
    let g0 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 0)) in
    let g1 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 1)) in
    equal_z3_formula f0 (neg b) &&
    equal_z3_formula g0 f0 &&
    equal_z3_formula g1 f1

  else
    equal_z3_formula f0 (neg b) &&
    check_negated_difference_singletons f_list g_list ass
  
(*Case 4:*)
let not_case (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  (*Format.printf "not \n";*)

  let b = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in

  if equalListLength then
    let g0 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 0)) in
    let g1 = strip_all_outer_double_neg (z3_of_literal (List.nth g_list 1)) in  
    equal_z3_formula f1 (neg b) &&
    equal_z3_formula g0 b &&
    equal_z3_formula g1 (neg b)

  else
    equal_z3_formula f1 (neg b) &&
    check_negated_difference_singletons f_list g_list ass

(*Case 5:*)
let andelim_aux (f_list : clause) : bool =
  let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
  match not_child f0 with
  | And aList ->
      let aList' = list_z3_formula_to_list aList in
      List.exists (fun x -> equal_z3_formula x f1) aList'
  | _ -> false

let andelim (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if equalListLength then
    if equal_clause f_list' g_list' then
      andelim_aux f_list
    else
      false
  else
    if check_negated_difference_singletons f_list g_list ass then
      andelim_aux f_list
    else
      false


(*
let andelim (f : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if equalListLength then

    if (equal_clause f_list' g_list') then
    
      let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
      let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
      match not_child f0 with
      | And aList ->
          let aList' = list_z3_formula_to_list aList in
          let rec find_match lst =
            match lst with
            | [] -> false
            | hd :: tl ->
                if equal_z3_formula hd f1 then true
                else find_match tl
          in
          find_match aList'
      | _ -> false
    else
      false

  else
    if (rUP_Checker (app f [f_list]) g_list) then
  
      let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
      let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
      match not_child f0 with
      | And aList ->
          let aList' = list_z3_formula_to_list aList in
          let rec find_match lst =
            match lst with
            | [] -> false
            | hd :: tl ->
                if equal_z3_formula hd f1 then true
                else find_match tl
          in
          find_match aList'
      | _ -> false
    else
      false
*)

(*Case 6:*)

let andintro_aux (f_list : clause) : bool =
  let len = List.length f_list in
  if len < 2 then false
  else
    let last = List.nth f_list (len - 1) in
    let rest = List.init (len - 1) (fun i -> List.nth f_list i) in
    let and_children = and_child_list last in
    equal_neg_list_formulas and_children rest

let andintro (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if List.length f_list < 2 then false
  else if equalListLength then
    if equal_clause f_list' g_list' then
      andintro_aux f_list
    else
      false
  else
    if check_negated_difference_singletons f_list g_list ass then
      andintro_aux f_list
    else
      false

(*
let andintro (f : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in
  (*Format.printf "andIntro \n";*)
  let len = List.length f_list in
  if len < 2 then false
  else
    let last = List.nth f_list (len - 1) in
    let rest = List.init (len - 1) (fun i -> List.nth f_list i) in

    if equalListLength then

      if (equal_clause f_list' g_list') then
        let and_children = and_child_list last in
        equal_neg_list_formulas and_children rest
      else
        false
    else
      if (rUP_Checker (app f [f_list]) g_list) then
        let and_children = and_child_list last in
        equal_neg_list_formulas and_children rest
      else
        false
*)

(*Case 7:*)
let orintro_aux (f_list : clause) : bool =
  let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
  let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
  match f1 with
  | Or aList ->
      let aList' = list_z3_formula_to_list aList in
      List.exists (fun x -> equal_z3_formula (neg x) f0) aList'
  | _ -> false

let orintro (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if equalListLength then
    if equal_clause f_list' g_list' then
      orintro_aux f_list
    else
      false
  else
    if check_negated_difference_singletons f_list g_list ass then
      orintro_aux f_list
    else
      false

(*
let orintro (f : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if equalListLength then

    if (equal_clause f_list' g_list') then

      let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
      let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
      match f1 with
      | Or aList ->
          let aList' = list_z3_formula_to_list aList in
          let rec find_match lst =
            match lst with
            | [] -> false
            | hd :: tl ->
                if equal_z3_formula (neg hd) f0 then true
                else find_match tl
          in
          find_match aList'
      | _ -> false
    else
      false

  else
    if (rUP_Checker (app f [f_list]) g_list) then

      let f0 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 0)) in
      let f1 = strip_all_outer_double_neg (z3_of_literal (List.nth f_list 1)) in
      match f1 with
      | Or aList ->
          let aList' = list_z3_formula_to_list aList in
          let rec find_match lst =
            match lst with
            | [] -> false
            | hd :: tl ->
                if equal_z3_formula (neg hd) f0 then true
                else find_match tl
          in
          find_match aList'
      | _ -> false
    else
      false
*)

(*Case 8:*)
let orelim_aux (f_list : clause) (len : int) : bool =
  let last = List.nth f_list (len - 1) in
  let rest = List.init (len - 1) (fun i -> List.nth f_list i) in
  let or_children = or_child_list last in
  equal_list_formulas or_children rest

let orelim (ass : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) (len : int) : bool =
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  if equalListLength then
    if equal_clause f_list' g_list' then
      orelim_aux f_list len
    else
      false
  else
    if check_negated_difference_singletons f_list g_list ass then
      orelim_aux f_list len
    else
      false

(*
let orelim (f : assumption) (f_list : clause) (g_list : clause) (equalListLength : bool) (len : int): bool =
  (*Format.printf "orElim \n";*)
  let f_list' = List.sort compare_literal f_list in
  let g_list' = List.sort compare_literal g_list in

  let last = List.nth f_list (len - 1) in
  let rest = List.init (len - 1) (fun i -> List.nth f_list i) in

  if equalListLength then
    if (equal_clause f_list' g_list') then
      let or_children = or_child_list last in
      equal_list_formulas or_children rest
    else
      false
  else 
    if (rUP_Checker (app f [f_list]) g_list) then
      let or_children = or_child_list last in
      equal_list_formulas or_children rest
    else
      false
*)

(* Main Tseitin checker *)
let tseitin_checker (f : assumption) (f_list : clause) (g_list : clause) : bool =
  let len_f = List.length f_list in
  let len_g = List.length g_list in
  let equalListLength = len_f = len_g in

  if len_f < 2 then false

  else
    (* Case 1: tseitinImpElim *)
    let case1 () =
    if len_f == 3 then
      match List.nth f_list 0 with
      | Neg (Pos_imply (a, b)) ->
          impelim f f_list g_list equalListLength
      | _ -> false
    else false
    in

    (* Case 2: tseitinImpIntro1 *)
    let case2 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 1) with
      | Imply (a, b) ->
          impintro f f_list g_list equalListLength
      | _ -> false
    else false
    in

    (* Case 3: tseitinImpIntro2 *)
    let case3 () =
      if len_f = 2 then
        match z3_of_literal (List.nth f_list 1) with
        | Imply (a, b) ->
            impintro2 f f_list g_list equalListLength
        | _ -> false
      else false
    in

    (* Case 4: tseitinNot *)
    let case4 () =
      if len_f = 2 then
        match z3_of_literal (List.nth f_list 1) with
        | Not b' ->
            not_case f f_list g_list equalListLength
        | b' ->
            not_case f f_list g_list equalListLength
      else false
    in

    (* Case 5: tseitinAndElim *)
    let case5 () =
      if len_f = 2 then
        match z3_of_literal (List.nth f_list 0) with
        | Not andf when matches_and andf ->
            andelim f f_list g_list equalListLength
        | _ -> false
      else false
    in

    (* Case 6: tseitinAndIntro *)
    let case6 () =
      if len_f >= 2 then
        match z3_of_literal (List.nth f_list (len_f - 1)) with
        | And aList ->
            andintro f f_list g_list equalListLength
        | _ -> false
      else false
    in

    (* Case 7: tseitinOrIntro *)
    let case7 () =
      if len_f = 2 then
        match z3_of_literal (List.nth f_list 1) with
        | Or aList ->
            orintro f f_list g_list equalListLength
        | _ -> false
      else false
    in

    (* Case 8: tseitinOrElim *)
    let case8 () =
      if len_f >= 2 then
        match z3_of_literal (List.nth f_list (len_f - 1)) with
        | Not (Or aList) ->
            orelim f f_list g_list equalListLength len_f
        | _ -> false
      else false
    in

    (* Try all cases *)
    List.exists (fun case -> case ()) [case1; case2; case3; case4; case5; case6; case7; case8]
