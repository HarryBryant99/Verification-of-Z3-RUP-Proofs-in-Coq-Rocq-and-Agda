
type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m
 end

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
| And of listZ3_Formula
| Or of listZ3_Formula
| Imply of z3_Formula * z3_Formula
| Not of z3_Formula
and listZ3_Formula =
| Lnil
| Lcons of z3_Formula * listZ3_Formula

type pos_Z3_Formula =
| Pos_z3var of z3_Variable
| Pos_and of listZ3_Formula
| Pos_or of listZ3_Formula
| Pos_imply of z3_Formula * z3_Formula

type literal =
| Pos of pos_Z3_Formula
| Neg of pos_Z3_Formula

type clause = literal list

type formula = clause list

type tseitinStep =
| TseitinNot of z3_Formula
| TseitinImpElim of z3_Formula * z3_Formula
| TseitinImpIntro1 of z3_Formula * z3_Formula
| TseitinImpIntro2 of z3_Formula * z3_Formula
| TseitinImpIntro3 of z3_Formula * z3_Formula
| TseitinAndIntro of listZ3_Formula
| TseitinAndElim of listZ3_Formula * nat
| TseitinOrIntro of listZ3_Formula * nat
| TseitinOrElim of listZ3_Formula

type zProofItem =
| TseitinStep of tseitinStep
| AssumptionZ3 of listZ3_Formula
| RupZ3proof of listZ3_Formula
| TseitinStepRed of tseitinStep * listZ3_Formula

type zProof = zProofItem list

type zClause = listZ3_Formula

(** val false_string : char list **)

let false_string =
  'F'::('A'::('L'::('S'::('E'::[]))))

(** val falseFor : z3_Formula **)

let falseFor =
  Z3var false_string

(** val negFor : z3_Formula -> z3_Formula **)

let negFor f = match f with
| Not x -> x
| _ -> Not f

(** val andFor : zClause -> z3_Formula **)

let andFor l =
  And l

(** val orFor : zClause -> z3_Formula **)

let orFor l =
  Or l

(** val nthWithDefault : nat -> zClause -> z3_Formula -> z3_Formula **)

let rec nthWithDefault n l default =
  match n with
  | O -> (match l with
          | Lnil -> default
          | Lcons (x, _) -> x)
  | S n' ->
    (match l with
     | Lnil -> default
     | Lcons (_, xs) -> nthWithDefault n' xs default)

(** val negForList : zClause -> zClause **)

let rec negForList = function
| Lnil -> Lnil
| Lcons (a, rest) -> Lcons ((negFor a), (negForList rest))

(** val tseitinNot2For : z3_Formula -> zClause **)

let tseitinNot2For a =
  Lcons (a, (Lcons ((negFor a), Lnil)))

(** val tseitinImpElim2For : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpElim2For a b =
  Lcons ((negFor a), (Lcons (b, (Lcons ((Not (Imply (a, b))), Lnil)))))

(** val tseitinImpIntro1toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro1toFor a b =
  Lcons (a, (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinImpIntro2toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro2toFor a b =
  Lcons ((negFor b), (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinImpIntro3toFor : z3_Formula -> z3_Formula -> zClause **)

let tseitinImpIntro3toFor a b =
  Lcons ((Not b), (Lcons ((Imply (a, b)), Lnil)))

(** val tseitinAndIntro2ForOpt : zClause -> zClause **)

let tseitinAndIntro2ForOpt l =
  Lcons ((andFor l), (negForList l))

(** val tseitinAndElim2For : zClause -> nat -> zClause **)

let tseitinAndElim2For l i =
  Lcons ((nthWithDefault i l falseFor), (Lcons ((Not (andFor l)), Lnil)))

(** val tseitinOrIntro2For : zClause -> nat -> zClause **)

let tseitinOrIntro2For l i =
  Lcons ((negFor (nthWithDefault i l falseFor)), (Lcons ((orFor l), Lnil)))

(** val tseitinOrElim2ForOpt : zClause -> zClause **)

let tseitinOrElim2ForOpt l =
  Lcons ((Not (orFor l)), l)

(** val tseitinProofItem2ConclusionOpt : tseitinStep -> zClause **)

let tseitinProofItem2ConclusionOpt = function
| TseitinNot a -> tseitinNot2For a
| TseitinImpElim (a, b) -> tseitinImpElim2For a b
| TseitinImpIntro1 (a, b) -> tseitinImpIntro1toFor a b
| TseitinImpIntro2 (a, b) -> tseitinImpIntro2toFor a b
| TseitinImpIntro3 (a, b) -> tseitinImpIntro3toFor a b
| TseitinAndIntro l -> tseitinAndIntro2ForOpt l
| TseitinAndElim (l, i) -> tseitinAndElim2For l i
| TseitinOrIntro (l, i) -> tseitinOrIntro2For l i
| TseitinOrElim l -> tseitinOrElim2ForOpt l

(** val zProofItem2ConclusionOpt : zProofItem -> zClause **)

let zProofItem2ConclusionOpt = function
| TseitinStep a -> tseitinProofItem2ConclusionOpt a
| AssumptionZ3 a -> a
| RupZ3proof a -> a
| TseitinStepRed (_, c) -> c

(** val length_listZ3 : zClause -> nat **)

let rec length_listZ3 = function
| Lnil -> O
| Lcons (_, rest) -> S (length_listZ3 rest)

(** val z3_formula_eq : z3_Formula -> z3_Formula -> bool **)

let rec z3_formula_eq f1 f2 =
  match f1 with
  | Z3var x -> (match f2 with
                | Z3var y -> eqb x y
                | _ -> false)
  | And l1 -> (match f2 with
               | And l2 -> list_z3_formula_eq l1 l2
               | _ -> false)
  | Or l1 -> (match f2 with
              | Or l2 -> list_z3_formula_eq l1 l2
              | _ -> false)
  | Imply (a1, b1) ->
    (match f2 with
     | Imply (a2, b2) -> (&&) (z3_formula_eq a1 a2) (z3_formula_eq b1 b2)
     | _ -> false)
  | Not f1' -> (match f2 with
                | Not f2' -> z3_formula_eq f1' f2'
                | _ -> false)

(** val list_z3_formula_eq : listZ3_Formula -> listZ3_Formula -> bool **)

and list_z3_formula_eq l1 l2 =
  match l1 with
  | Lnil -> (match l2 with
             | Lnil -> true
             | Lcons (_, _) -> false)
  | Lcons (h1, t1) ->
    (match l2 with
     | Lnil -> false
     | Lcons (h2, t2) -> (&&) (z3_formula_eq h1 h2) (list_z3_formula_eq t1 t2))

(** val pos_z3_formula_eq : pos_Z3_Formula -> pos_Z3_Formula -> bool **)

let pos_z3_formula_eq p1 p2 =
  match p1 with
  | Pos_z3var x -> (match p2 with
                    | Pos_z3var y -> eqb x y
                    | _ -> false)
  | Pos_and l1 ->
    (match p2 with
     | Pos_and l2 -> list_z3_formula_eq l1 l2
     | _ -> false)
  | Pos_or l1 ->
    (match p2 with
     | Pos_or l2 -> list_z3_formula_eq l1 l2
     | _ -> false)
  | Pos_imply (l1, l2) ->
    (match p2 with
     | Pos_imply (l3, l4) -> (&&) (z3_formula_eq l1 l3) (z3_formula_eq l2 l4)
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

type assumption = clause list

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

(** val zfor2Lit : z3_Formula -> literal **)

let rec zfor2Lit = function
| Z3var v -> Pos (Pos_z3var v)
| And l -> Pos (Pos_and l)
| Or l -> Pos (Pos_or l)
| Imply (a, b) -> Pos (Pos_imply (a, b))
| Not x ->
  (match x with
   | Z3var v -> Neg (Pos_z3var v)
   | And l -> Neg (Pos_and l)
   | Or l -> Neg (Pos_or l)
   | Imply (a, b) -> Neg (Pos_imply (a, b))
   | Not y -> zfor2Lit y)

(** val zCl2RClause : zClause -> clause **)

let rec zCl2RClause = function
| Lnil -> []
| Lcons (x, xs) -> (zfor2Lit x) :: (zCl2RClause xs)

(** val zListCl2RListCl : zClause list -> clause list **)

let rec zListCl2RListCl = function
| [] -> []
| x :: xs -> (zCl2RClause x) :: (zListCl2RListCl xs)

(** val zProof2ConclusionOpt : zProof -> zClause list **)

let rec zProof2ConclusionOpt = function
| [] -> []
| x :: xs -> (zProofItem2ConclusionOpt x) :: (zProof2ConclusionOpt xs)

(** val in_listZ3b : z3_Formula -> listZ3_Formula -> bool **)

let rec in_listZ3b x = function
| Lnil -> false
| Lcons (y, ys) -> (||) (z3_formula_eq x y) (in_listZ3b x ys)

(** val listZ3_subset : listZ3_Formula -> listZ3_Formula -> bool **)

let rec listZ3_subset l1 l2 =
  match l1 with
  | Lnil -> true
  | Lcons (x, xs) -> (&&) (in_listZ3b x l2) (listZ3_subset xs l2)

(** val negSingletons : listZ3_Formula -> listZ3_Formula list **)

let rec negSingletons = function
| Lnil -> []
| Lcons (f, rest) -> (Lcons ((negFor f), Lnil)) :: (negSingletons rest)

(** val in_listZ3List : listZ3_Formula -> listZ3_Formula list -> bool **)

let rec in_listZ3List x = function
| [] -> false
| y :: ys -> (||) (list_z3_formula_eq x y) (in_listZ3List x ys)

(** val listZ3List_subset :
    listZ3_Formula list -> listZ3_Formula list -> bool **)

let rec listZ3List_subset l1 l2 =
  match l1 with
  | [] -> true
  | x :: xs -> (&&) (in_listZ3List x l2) (listZ3List_subset xs l2)

(** val setminus : listZ3_Formula -> listZ3_Formula -> listZ3_Formula **)

let rec setminus a b =
  match a with
  | Lnil -> Lnil
  | Lcons (x, xs) ->
    if in_listZ3b x b then setminus xs b else Lcons (x, (setminus xs b))

(** val zProofCheckTseitin : tseitinStep -> bool **)

let zProofCheckTseitin = function
| TseitinAndElim (l, i) -> Nat.ltb i (length_listZ3 l)
| TseitinOrIntro (l, i) -> Nat.ltb i (length_listZ3 l)
| _ -> true

(** val zProofCheckLastStep : zClause list -> zProofItem -> bool **)

let zProofCheckLastStep cl = function
| TseitinStep a -> zProofCheckTseitin a
| AssumptionZ3 _ -> true
| RupZ3proof l -> rUP_Checker (zListCl2RListCl cl) (zCl2RClause l)
| TseitinStepRed (a, c) ->
  (&&)
    ((&&) (listZ3_subset c (tseitinProofItem2ConclusionOpt a))
      (listZ3List_subset
        (negSingletons (setminus (tseitinProofItem2ConclusionOpt a) c)) cl))
    (zProofCheckTseitin a)

(** val zProofCheck : zProof -> bool **)

let rec zProofCheck = function
| [] -> true
| x :: xs ->
  (&&) (zProofCheckLastStep (zProof2ConclusionOpt xs) x) (zProofCheck xs)

type zProofCheckResult =
  | Passed
  | Failed of zProofItem

let rec zProofCheckWithFailure lst =
  match lst with
  | [] -> Passed
  | x :: xs ->
      let cl = zProof2ConclusionOpt xs in
      let remaining = List.length lst in
      if remaining mod 1000 = 0 then
        Printf.printf "Steps remaining: %d\n%!" remaining;
      if zProofCheckLastStep cl x then
        zProofCheckWithFailure xs
      else
        Failed x