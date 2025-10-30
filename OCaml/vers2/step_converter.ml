open Proven_sat_checker
open Types

(* Compare two z3_Formula values *)
let rec compare_z3_formula f1 f2 =
  match f1, f2 with
  | Z3var x, Z3var y -> compare x y
  | Not a, Not b -> compare_z3_formula a b
  | And l1, And l2 -> compare_list_z3_formula l1 l2
  | Or l1, Or l2 -> compare_list_z3_formula l1 l2
  | Imply (a1, b1), Imply (a2, b2) ->
      let cmp_a = compare_z3_formula a1 a2 in
      if cmp_a <> 0 then cmp_a else compare_z3_formula b1 b2
  (* Ordering fallback for different constructors *)
  | Z3var _, _ -> -1
  | _, Z3var _ -> 1
  | Not _, _ -> -1
  | _, Not _ -> 1
  | And _, _ -> -1
  | _, And _ -> 1
  | Or _, _ -> -1
  | _, Or _ -> 1

(* Compare two listZ3_Formula values *)
and compare_list_z3_formula l1 l2 =
  match l1, l2 with
  | Lnil, Lnil -> 0
  | Lnil, _ -> -1
  | _, Lnil -> 1
  | Lcons (h1, t1), Lcons (h2, t2) ->
      let cmp_h = compare_z3_formula h1 h2 in
      if cmp_h <> 0 then cmp_h else compare_list_z3_formula t1 t2

let equal_z3_formula f1 f2 =
  compare_z3_formula f1 f2 = 0

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

let rec list_z3_formula_to_list (lst : listZ3_Formula) : z3_Formula list =
  match lst with
  | Lnil -> []
  | Lcons (h, t) -> h :: list_z3_formula_to_list t

let and_child_list (f : z3_Formula) : listZ3_Formula =
  match f with
  | And lst -> lst
  | _ -> failwith "Expected an And formula"

let or_child_list (f : z3_Formula) : listZ3_Formula =
  match f with
  | Or lst -> lst
  | _ -> failwith "Expected an Or formula"

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

let rec nat_to_int (n : nat) : int =
  match n with
  | O -> 0
  | S n' -> 1 + nat_to_int n'

let equal_listZ3_formula_unordered (l1 : listZ3_Formula) (l2 : listZ3_Formula) : bool =
  let sorted1 = List.sort compare_z3_formula (list_z3_formula_to_list l1) in
  let sorted2 = List.sort compare_z3_formula (list_z3_formula_to_list l2) in
  sorted1 = sorted2

let rec length_listZ3 (lst : listZ3_Formula) : int =
  match lst with
  | Lnil -> 0
  | Lcons (_, rest) -> 1 + length_listZ3 rest

let rec nth_listZ3 (lst : listZ3_Formula) (n : int) : z3_Formula =
  match lst, n with
  | Lnil, _ -> failwith "Index out of bounds"
  | Lcons (h, _), 0 -> h
  | Lcons (_, t), n when n > 0 -> nth_listZ3 t (n - 1)
  | _, _ -> failwith "Invalid index"

let rec strip_all_outer_double_neg (f : z3_Formula) : z3_Formula =
  match f with
  | Not (Not inner) -> strip_all_outer_double_neg inner
  | _ -> f


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


let tseitin_sorter (f_list : listZ3_Formula) (g_list : listZ3_Formula) : bool * tseitinStep option =
  let len_f = length_listZ3 f_list in
  let find_index_equal_z3 (a : z3_Formula) (lst : listZ3_Formula) : nat =
  let rec aux i = function
    | Lnil -> i  (* or O if you want to indicate "not found" *)
    | Lcons (x, xs) -> if x = a then i else aux (S i) xs
  in
  aux O lst
  in

  let case1 () =
    if len_f = 3 then
      match nth_listZ3 f_list 0 with
      | Not (Imply (a, b)) ->
        let a' = imp_child1 (not_child (nth_listZ3 f_list 0)) in
        let b' = imp_child2 (not_child (nth_listZ3 f_list 0)) in
        if ((nth_listZ3 f_list 1) = (negFor a')) && ((nth_listZ3 f_list 2) = b') then
          (true, Some (TseitinImpElim (a, b)))
        else
          (false, None)
      | _ -> (false, None)
    else
      (false, None)
  in
  let case2 () =
    if len_f = 2 then
      match (nth_listZ3 f_list 1) with
      | Imply (a, b) ->
        let a' = imp_child1 (nth_listZ3 f_list 1) in
        if ((nth_listZ3 f_list 0) = a') then
          (true, Some (TseitinImpIntro1 (a,b)))
        else
          (false, None)
      | _ -> (false, None)
    else (false, None)
  in

  let case3 () =
    if len_f = 2 then
      match (nth_listZ3 f_list 1) with
      | Imply (a, b) ->
        let b' = imp_child2 (nth_listZ3 f_list 1) in
        if ((nth_listZ3 f_list 0) = (negFor b')) then
          (true, Some (TseitinImpIntro2 (a,b)))
        else
          (false, None)
      | _ -> (false, None)
    else (false, None)
  in

  let case4 () =
    if len_f = 2 then
      match (nth_listZ3 f_list 1) with
      | Not b' ->
        let a' = not_child(nth_listZ3 f_list 1) in
        if ((nth_listZ3 f_list 0) = a') then
          (true, Some (TseitinNot b'))
        else
          (false, None)
      | b' ->
        if ((nth_listZ3 f_list 0) = (negFor b')) then
          (true, Some (TseitinNot b'))
        else
          (false, None)
    else (false, None)
  in

  let case5 () =
    if len_f = 2 then
      match (nth_listZ3 f_list 0) with
      | Not andf when matches_and andf ->
        let al = (and_child_list (not_child (nth_listZ3 f_list 0))) in
        let b = nth_listZ3 f_list 1 in
        let i = find_index_equal_z3 b al in
        let i' = nat_to_int i in
        if (0 <= i') && (i' < (length_listZ3 al)) then
          (true, Some (TseitinAndElim (al, i)))
        else (false, None)
      | _ -> (false, None)
    else (false, None)
  in

  let case6 () =
    if len_f >= 2 then
      match (nth_listZ3 f_list (len_f - 1)) with
      | And aList ->
        (true, Some (TseitinAndIntro aList))
      | _ -> (false, None)
    else (false, None)
  in

  let case7 () =
    if len_f = 2 then
      match (nth_listZ3 f_list 1) with
      | Or aList ->
        let ol = (or_child_list (nth_listZ3 f_list 1)) in
        let b = nth_listZ3 f_list 0 in
        let i = find_index_equal_z3 (negFor b) ol in
        let i' = nat_to_int i in
        if (0 <= i') && (i' < (length_listZ3 ol)) then
          (true, Some (TseitinOrIntro (ol,i)))
        else (false, None)
      | _ -> (false, None)
    else (false, None)
  in

  let case8 () =
    if len_f >= 2 then
      match (nth_listZ3 f_list (len_f - 1)) with
      | Not (Or aList) ->
        (true, Some (TseitinOrElim aList))
      | _ -> (false, None)
    else (false, None)
  in

  let cases = [case1; case2; case3; case4; case5; case6; case7; case8] in
  let rec try_cases = function
    | [] -> (false, None)
    | case :: rest ->
      match case () with
      | (true, Some _) as result -> result
      | _ -> try_cases rest
  in
  try_cases cases

let step_processor (s : item) : zProofItem =
  match s with
  | Assumption clause ->
      AssumptionZ3 clause
  | Rup clause ->
      RupZ3proof clause
  | Tseitin (f_list, g_list) ->
      let equalList = equal_listZ3_formula_unordered f_list g_list in
      let (success, step_opt) = tseitin_sorter f_list g_list in
      match (equalList, success, step_opt) with
      | (true, true, Some step) -> TseitinStep step
      | (false, true, Some step) -> TseitinStepRed (step, g_list)
      | _ -> failwith "Invalid Tseitin step: could not process"

let process_items (items : item list) : zProofItem list =
  List.mapi (fun i item ->
    if i mod 10000 = 0 then
      Printf.printf "Processing item %d\n%!" i;
    step_processor item
  ) items


(*
let tseitin_sorter (f_list : clause) (g_list : clause) : zProofItem =
  let f' = List.sort compare_literal f_list in
  let g' = List.sort compare_literal g_list in
  let equalList = equal_clause f' g' in
  let len_f = List.length f_list in

  (* Helper to find index of literal in a list *)
  let find_index_equal a lst =
    let rec aux i = function
      | [] -> -1
      | x :: xs -> if x = a then i else aux (i + 1) xs
    in
    aux 0 lst
  in

  (* Case 1: tseitinImpElim *)
  let case1 () =
    if len_f = 3 then
      match List.nth f_list 0 with
      | Neg (Pos_imply (a, b)) ->
        if equalList then TseitinStep (TseitinImpElim a b)
        else TseitinStepRed (TseitinImpElim a b) g_list
      | _ -> false
    else false
  in

  (* Case 2: tseitinImpIntro1 *)
  let case2 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 1) with
      | Imply (a, b) ->
        if equalList then TseitinStep (TseitinImpIntro1 a b)
        else TseitinStepRed (TseitinImpIntro1 a b) g_list
      | _ -> false
    else false
  in

  (* Case 3: tseitinImpIntro2 *)
  let case3 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 1) with
      | Imply (a, b) ->
        if equalList then TseitinStep (TseitinImpIntro2 a b)
        else TseitinStepRed (TseitinImpIntro2 a b) g_list
      | _ -> false
    else false
  in

  (* Case 4: tseitinNot *)
  let case4 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 1) with
      | Not b' ->
        if equalList then TseitinStep (TseitinNot b')
        else TseitinStepRed (TseitinNot b') g_list
      | b' ->
        if equalList then TseitinStep (TseitinNot b')
        else TseitinStepRed (TseitinNot b') g_list
    else false
  in

  (* Case 5: tseitinAndElim *)
  let case5 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 0) with
      | Not andf when matches_and andf ->
        let b = List.nth f_list 1 in
        let i = find_index_equal b (and_child_list andf) in
        if i >= 0 then
          if equalList then TseitinStep (TseitinAndElim andf i)
          else TseitinStepRed (TseitinAndElim andf i) g_list
        else false
      | _ -> false
    else false
  in

  (* Case 6: tseitinAndIntro *)
  let case6 () =
    if len_f >= 2 then
      match z3_of_literal (List.nth f_list (len_f - 1)) with
      | And aList ->
        if equalList then TseitinStep (TseitinAndIntro aList)
        else TseitinStepRed (TseitinAndIntro aList) g_list
      | _ -> false
    else false
  in

  (* Case 7: tseitinOrIntro *)
  let case7 () =
    if len_f = 2 then
      match z3_of_literal (List.nth f_list 1) with
      | Or aList ->
        let b = List.nth f_list 0 in
        let i = find_index_equal b (or_child_list aList) in
        if i >= 0 then
          if equalList then TseitinStep (TseitinOrIntro aList i)
          else TseitinStepRed (TseitinOrIntro aList i) g_list
        else false
      | _ -> false
    else false
  in

  (* Case 8: tseitinOrElim *)
  let case8 () =
    if len_f >= 2 then
      match z3_of_literal (List.nth f_list (len_f - 1)) with
      | Not (Or aList) ->
        if equalList then TseitinStep (TseitinOrElim aList)
        else TseitinStepRed (TseitinOrElim aList) g_list
      | _ -> false
    else false
  in

  (* Try all cases in order *)
  let cases = [case1; case2; case3; case4; case5; case6; case7; case8] in
  let rec try_cases = function
    | [] -> TseitinNone
    | case :: rest ->
      match case () with
      | TseitinNone -> try_cases rest
      | result -> result
  in
  try_cases cases
*)
