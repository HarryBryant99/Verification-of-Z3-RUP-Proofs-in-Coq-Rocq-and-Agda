
type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

type z3_Variable = char list

type z3_Formula =
| Z3var of z3_Variable
| And of z3_Formula list
| Or of z3_Formula list
| Imply of z3_Formula list
| Not of z3_Formula

type pos_Z3_Formula =
| Pos_z3var of z3_Variable
| Pos_and of z3_Formula list
| Pos_or of z3_Formula list
| Pos_imply of z3_Formula list

type literal =
| Pos of pos_Z3_Formula
| Neg of pos_Z3_Formula

type clause = literal list

type formula = clause list

type assumption = formula

(** val z3_formula_eq : z3_Formula -> z3_Formula -> bool **)

let rec z3_formula_eq f1 f2 =
  match f1 with
  | Z3var x -> (match f2 with
                | Z3var y -> eqb x y
                | _ -> false)
  | And l1 ->
    (match f2 with
     | And l2 ->
       list_eqb (Obj.magic z3_formula_eq) (Obj.magic l1) (Obj.magic l2)
     | _ -> false)
  | Or l1 ->
    (match f2 with
     | Or l2 ->
       list_eqb (Obj.magic z3_formula_eq) (Obj.magic l1) (Obj.magic l2)
     | _ -> false)
  | Imply l1 ->
    (match f2 with
     | Imply l2 ->
       list_eqb (Obj.magic z3_formula_eq) (Obj.magic l1) (Obj.magic l2)
     | _ -> false)
  | Not f1' -> (match f2 with
                | Not f2' -> z3_formula_eq f1' f2'
                | _ -> false)

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

and list_eqb eqb0 l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: xs1 ->
    (match l2 with
     | [] -> false
     | x2 :: xs2 -> (&&) (eqb0 x1 x2) (list_eqb eqb0 xs1 xs2))

(** val pos_z3_formula_eq : pos_Z3_Formula -> pos_Z3_Formula -> bool **)

let rec pos_z3_formula_eq p1 p2 =
  match p1 with
  | Pos_z3var x -> (match p2 with
                    | Pos_z3var y -> eqb x y
                    | _ -> false)
  | Pos_and l1 ->
    (match p2 with
     | Pos_and l2 -> list_eqb z3_formula_eq l1 l2
     | _ -> false)
  | Pos_or l1 ->
    (match p2 with
     | Pos_or l2 -> list_eqb z3_formula_eq l1 l2
     | _ -> false)
  | Pos_imply l1 ->
    (match p2 with
     | Pos_imply l2 -> list_eqb z3_formula_eq l1 l2
     | _ -> false)

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb l1 l2 =
  match l1 with
  | Pos p1 ->
    (match l2 with
     | Pos p2 -> pos_z3_formula_eq p1 p2
     | Neg _ -> false)
  | Neg p1 ->
    (match l2 with
     | Pos _ -> false
     | Neg p2 -> pos_z3_formula_eq p1 p2)

(** val negate : literal -> literal **)

let negate = function
| Pos x -> Neg x
| Neg x -> Pos x

type splitClauses = (clause list * literal list) * bool

type preparePropStep = (clause list * literal list) * literal

type splitLiterals = literal list * bool

(** val removeLitFromClause : literal -> clause -> clause **)

let rec removeLitFromClause l = function
| [] -> []
| hd :: tl ->
  let new_clause = removeLitFromClause l tl in
  if literal_eqb l hd then new_clause else hd :: new_clause

(** val lit_in_clause : literal -> clause -> bool **)

let lit_in_clause l c =
  existsb (literal_eqb l) c

(** val processOneClause_aux2 : clause -> literal -> bool -> clause **)

let processOneClause_aux2 c l = function
| true -> removeLitFromClause (negate l) c
| false -> c

(** val processOneClause_aux1 : clause -> literal -> bool -> clause option **)

let processOneClause_aux1 c l = function
| true -> None
| false -> Some (processOneClause_aux2 c l (lit_in_clause (negate l) c))

(** val processOneClause : clause -> literal -> clause option **)

let processOneClause c l =
  processOneClause_aux1 c l (lit_in_clause l c)

(** val processClausesaux : clause option -> clause list -> clause list **)

let processClausesaux c ih =
  match c with
  | Some c0 -> c0 :: ih
  | None -> ih

(** val processClauses : clause list -> literal -> clause list **)

let rec processClauses c l =
  match c with
  | [] -> []
  | hd :: tl ->
    processClausesaux (processOneClause hd l) (processClauses tl l)

(** val addClauseToSplitClauses : clause -> splitClauses -> splitClauses **)

let addClauseToSplitClauses clause0 = function
| (p, boolIH) ->
  let (clausesIH, literalsIH) = p in
  (match clause0 with
   | [] -> (([], []), true)
   | l :: l0 ->
     (match l0 with
      | [] -> ((clausesIH, (l :: literalsIH)), boolIH)
      | _ :: _ -> (((clause0 :: clausesIH), literalsIH), boolIH)))

(** val splitClauses0 : clause list -> splitClauses **)

let rec splitClauses0 = function
| [] -> (([], []), false)
| c :: cs -> addClauseToSplitClauses c (splitClauses0 cs)

(** val processAndSplitClausesWithLit :
    clause list -> literal -> splitClauses **)

let processAndSplitClausesWithLit clauses l =
  let processed_clauses = processClauses clauses l in
  splitClauses0 processed_clauses

(** val processListLitsWithLit : literal list -> literal -> splitLiterals **)

let rec processListLitsWithLit literals l =
  match literals with
  | [] -> ([], false)
  | hd :: tl ->
    if literal_eqb hd l
    then processListLitsWithLit tl l
    else if literal_eqb hd (negate l)
         then ([], true)
         else let (remaining_literals, found_negation) =
                processListLitsWithLit tl l
              in
              ((hd :: remaining_literals), found_negation)

(** val combineSplitClausesSplitLits :
    splitClauses -> splitLiterals -> splitClauses **)

let combineSplitClausesSplitLits sc rl =
  let (p, contains_empty) = sc in
  let (processed_clauses, unit_literals) = p in
  let (filtered_literals, found_negation) = rl in
  ((processed_clauses, (app unit_literals filtered_literals)),
  ((||) contains_empty found_negation))

(** val propagationStep' :
    clause list -> literal list -> literal -> splitClauses **)

let propagationStep' clauses literals l =
  combineSplitClausesSplitLits (processAndSplitClausesWithLit clauses l)
    (processListLitsWithLit literals l)

(** val propagationStep : preparePropStep -> splitClauses **)

let propagationStep = function
| (p0, l) -> let (c, ls) = p0 in propagationStep' c ls l

(** val selectAndRunPropagator :
    splitClauses -> (splitClauses -> splitClauses) -> splitClauses **)

let selectAndRunPropagator sc cont =
  let (p, b) = sc in
  let (c, ls) = p in
  if b
  then sc
  else (match ls with
        | [] -> sc
        | l :: ls0 -> cont (propagationStep ((c, ls0), l)))

(** val iteratePropagator : nat -> splitClauses -> splitClauses **)

let rec iteratePropagator n p =
  match n with
  | O -> p
  | S n0 -> selectAndRunPropagator p (iteratePropagator n0)

(** val splitClauses_to_bool : splitClauses -> bool **)

let splitClauses_to_bool = function
| (_, b) -> b

(** val literal_in_seen : literal -> pos_Z3_Formula list -> bool **)

let literal_in_seen l seen =
  match l with
  | Pos x -> existsb (pos_z3_formula_eq x) seen
  | Neg x -> existsb (pos_z3_formula_eq x) seen

(** val addVarsInClauseToSeen :
    clause -> pos_Z3_Formula list -> pos_Z3_Formula list **)

let rec addVarsInClauseToSeen c seen =
  match c with
  | [] -> seen
  | l :: ls ->
    let lit_str = match l with
                  | Pos x -> x
                  | Neg x -> x in
    if literal_in_seen l seen
    then addVarsInClauseToSeen ls seen
    else addVarsInClauseToSeen ls (lit_str :: seen)

(** val addVarsInForToSeen :
    formula -> pos_Z3_Formula list -> pos_Z3_Formula list **)

let rec addVarsInForToSeen f seen =
  match f with
  | [] -> seen
  | c :: cs ->
    let updated_seen = addVarsInClauseToSeen c seen in
    addVarsInForToSeen cs updated_seen

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val countVarsInFor : formula -> nat **)

let countVarsInFor f =
  length (addVarsInForToSeen f [])

(** val unitPropagationAndCheck : assumption -> bool **)

let unitPropagationAndCheck a =
  splitClauses_to_bool
    (iteratePropagator (countVarsInFor a) (splitClauses0 a))

(** val negate_clause : clause -> formula **)

let negate_clause c =
  map (fun l -> (negate l) :: []) c

(** val rUP_Checker : assumption -> clause -> bool **)

let rUP_Checker a c =
  unitPropagationAndCheck (app (negate_clause c) a)

type proofStep =
| Tseitin of (clause * clause)
| Rup of clause
| Assumption of clause
| Deletion of clause

type preProof = proofStep list

(** val clause_eqb : literal list -> literal list -> bool **)

let rec clause_eqb c1 c2 =
  match c1 with
  | [] -> (match c2 with
           | [] -> true
           | _ :: _ -> false)
  | l1 :: tl1 ->
    (match c2 with
     | [] -> false
     | l2 :: tl2 -> if literal_eqb l1 l2 then clause_eqb tl1 tl2 else false)

(** val remove_clause : clause -> formula -> formula **)

let rec remove_clause c = function
| [] -> []
| x :: xs ->
  if clause_eqb x c then remove_clause c xs else x :: (remove_clause c xs)

(** val checkProof : preProof -> formula -> bool * proofStep option **)
(*
let rec checkProof p f =
  match p with
  | [] -> (true, None)
  | step :: ps ->
    (match step with
     | Tseitin p0 -> let (_, c2) = p0 in checkProof ps (app f (c2 :: []))
     | Rup c ->
       if rUP_Checker f c
       then checkProof ps (app f (c :: []))
       else (false, (Some step))
     | Assumption a -> checkProof ps (app f (a :: []))
     | Deletion c -> checkProof ps (remove_clause c f))
*)