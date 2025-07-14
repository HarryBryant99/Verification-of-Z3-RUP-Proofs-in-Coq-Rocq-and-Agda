
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString -> (match s2 with
                    | EmptyString -> True
                    | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

type literal =
| Pos of string
| Neg of string

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb l1 l2 =
  match l1 with
  | Pos s1 -> (match l2 with
               | Pos s2 -> eqb1 s1 s2
               | Neg _ -> False)
  | Neg s1 -> (match l2 with
               | Pos _ -> False
               | Neg s2 -> eqb1 s1 s2)

(** val negate : literal -> literal **)

let negate = function
| Pos x -> Neg x
| Neg x -> Pos x

type clause = literal list

type formula = clause list

type assumption = formula

type splitClauses = ((clause list, literal list) prod, bool) prod

type preparePropStep = ((clause list, literal list) prod, literal) prod

type splitLiterals = (literal list, bool) prod

(** val removeLitFromClause : literal -> clause -> clause **)

let rec removeLitFromClause l = function
| Nil -> Nil
| Cons (hd, tl) ->
  let new_clause = removeLitFromClause l tl in
  (match literal_eqb l hd with
   | True -> new_clause
   | False -> Cons (hd, new_clause))

(** val lit_in_clause : literal -> clause -> bool **)

let lit_in_clause l c =
  existsb (literal_eqb l) c

(** val processOneClause_aux2 : clause -> literal -> bool -> clause **)

let processOneClause_aux2 c l = function
| True -> removeLitFromClause (negate l) c
| False -> c

(** val processOneClause_aux1 : clause -> literal -> bool -> clause option **)

let processOneClause_aux1 c l = function
| True -> None
| False -> Some (processOneClause_aux2 c l (lit_in_clause (negate l) c))

(** val processOneClause : clause -> literal -> clause option **)

let processOneClause c l =
  processOneClause_aux1 c l (lit_in_clause l c)

(** val processClausesaux : clause option -> clause list -> clause list **)

let processClausesaux c ih =
  match c with
  | Some c0 -> Cons (c0, ih)
  | None -> ih

(** val processClauses : clause list -> literal -> clause list **)

let rec processClauses c l =
  match c with
  | Nil -> Nil
  | Cons (hd, tl) ->
    processClausesaux (processOneClause hd l) (processClauses tl l)

(** val addClauseToSplitClauses : clause -> splitClauses -> splitClauses **)

let addClauseToSplitClauses clause0 = function
| Pair (p, boolIH) ->
  let Pair (clausesIH, literalsIH) = p in
  (match clause0 with
   | Nil -> Pair ((Pair (Nil, Nil)), True)
   | Cons (l, l0) ->
     (match l0 with
      | Nil -> Pair ((Pair (clausesIH, (Cons (l, literalsIH)))), boolIH)
      | Cons (_, _) ->
        Pair ((Pair ((Cons (clause0, clausesIH)), literalsIH)), boolIH)))

(** val splitClauses0 : clause list -> splitClauses **)

let rec splitClauses0 = function
| Nil -> Pair ((Pair (Nil, Nil)), False)
| Cons (c, cs) -> addClauseToSplitClauses c (splitClauses0 cs)

(** val processAndSplitClausesWithLit :
    clause list -> literal -> splitClauses **)

let processAndSplitClausesWithLit clauses l =
  let processed_clauses = processClauses clauses l in
  splitClauses0 processed_clauses

(** val processListLitsWithLit : literal list -> literal -> splitLiterals **)

let rec processListLitsWithLit literals l =
  match literals with
  | Nil -> Pair (Nil, False)
  | Cons (hd, tl) ->
    (match literal_eqb hd l with
     | True -> processListLitsWithLit tl l
     | False ->
       (match literal_eqb hd (negate l) with
        | True -> Pair (Nil, True)
        | False ->
          let Pair (remaining_literals, found_negation) =
            processListLitsWithLit tl l
          in
          Pair ((Cons (hd, remaining_literals)), found_negation)))

(** val combineSplitClausesSplitLits :
    splitClauses -> splitLiterals -> splitClauses **)

let combineSplitClausesSplitLits sc rl =
  let Pair (p, contains_empty) = sc in
  let Pair (processed_clauses, unit_literals) = p in
  let Pair (filtered_literals, found_negation) = rl in
  Pair ((Pair (processed_clauses, (app unit_literals filtered_literals))),
  (match contains_empty with
   | True -> True
   | False -> found_negation))

(** val propagationStep' :
    clause list -> literal list -> literal -> splitClauses **)

let propagationStep' clauses literals l =
  combineSplitClausesSplitLits (processAndSplitClausesWithLit clauses l)
    (processListLitsWithLit literals l)

(** val propagationStep : preparePropStep -> splitClauses **)

let propagationStep = function
| Pair (p0, l) -> let Pair (c, ls) = p0 in propagationStep' c ls l

(** val selectAndRunPropagator :
    splitClauses -> (splitClauses -> splitClauses) -> splitClauses **)

let selectAndRunPropagator sc cont =
  let Pair (p, b) = sc in
  let Pair (c, ls) = p in
  (match b with
   | True -> sc
   | False ->
     (match ls with
      | Nil -> sc
      | Cons (l, ls0) -> cont (propagationStep (Pair ((Pair (c, ls0)), l)))))

(** val iteratePropagator : nat -> splitClauses -> splitClauses **)

let rec iteratePropagator n p =
  match n with
  | O -> p
  | S n0 -> selectAndRunPropagator p (iteratePropagator n0)

(** val splitClauses_to_bool : splitClauses -> bool **)

let splitClauses_to_bool = function
| Pair (_, b) -> b

(** val literal_in_seen : literal -> string list -> bool **)

let literal_in_seen l seen =
  match l with
  | Pos x -> existsb (eqb1 x) seen
  | Neg x -> existsb (eqb1 x) seen

(** val addVarsInClauseToSeen : clause -> string list -> string list **)

let rec addVarsInClauseToSeen c seen =
  match c with
  | Nil -> seen
  | Cons (l, ls) ->
    let lit_str = match l with
                  | Pos x -> x
                  | Neg x -> x in
    (match literal_in_seen l seen with
     | True -> addVarsInClauseToSeen ls seen
     | False -> addVarsInClauseToSeen ls (Cons (lit_str, seen)))

(** val addVarsInForToSeen : formula -> string list -> string list **)

let rec addVarsInForToSeen f seen =
  match f with
  | Nil -> seen
  | Cons (c, cs) ->
    let updated_seen = addVarsInClauseToSeen c seen in
    addVarsInForToSeen cs updated_seen

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val countVarsInFor : formula -> nat **)

let countVarsInFor f =
  length (addVarsInForToSeen f Nil)

(** val unitPropagationAndCheck : assumption -> bool **)

let unitPropagationAndCheck a =
  splitClauses_to_bool (iteratePropagator (countVarsInFor a) (splitClauses0 a))

(** val clause_eqb : literal list -> literal list -> bool **)

let rec clause_eqb c1 c2 =
  match c1 with
  | Nil -> (match c2 with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (l1, tl1) ->
    (match c2 with
     | Nil -> False
     | Cons (l2, tl2) ->
       (match literal_eqb l1 l2 with
        | True -> clause_eqb tl1 tl2
        | False -> False))

(** val negate_clause : clause -> formula **)

let negate_clause c =
  map (fun l -> Cons ((negate l), Nil)) c

(** val rUP_Checker : assumption -> clause -> bool **)

let rUP_Checker a c =
  unitPropagationAndCheck (app (negate_clause c) a)

type rupProofStep =
| Ass' of clause
| Rup' of clause

type rupProof = rupProofStep list

(** val rupProof2Assumptions : rupProof -> clause list **)

let rec rupProof2Assumptions = function
| Nil -> Nil
| Cons (p, pl0) ->
  (match p with
   | Ass' c -> Cons (c, (rupProof2Assumptions pl0))
   | Rup' _ -> rupProof2Assumptions pl0)

(** val rupProof2AssumptionsRevFirst : rupProof -> clause list **)

let rupProof2AssumptionsRevFirst pl =
  rupProof2Assumptions (rev pl)

(** val rupProof2Conclusions : rupProof -> clause list **)

let rec rupProof2Conclusions = function
| Nil -> Nil
| Cons (p, pl0) ->
  (match p with
   | Ass' c -> Cons (c, (rupProof2Conclusions pl0))
   | Rup' c -> Cons (c, (rupProof2Conclusions pl0)))

(** val rupProof2ConclusionsRevFirst : rupProof -> clause list **)

let rupProof2ConclusionsRevFirst pl =
  rupProof2Conclusions (rev pl)

(** val rupProofChecker : rupProof -> bool **)

let rec rupProofChecker = function
| Nil -> True
| Cons (p, pl0) ->
  (match p with
   | Ass' _ -> rupProofChecker pl0
   | Rup' c ->
     (match rUP_Checker (rupProof2Conclusions pl0) c with
      | True -> rupProofChecker pl0
      | False -> False))

(** val rupProofCheckerRevFirst : rupProof -> bool **)

let rupProofCheckerRevFirst pl =
  rupProofChecker (rev pl)

(** val isEmpty : clause -> bool **)

let isEmpty = function
| Nil -> True
| Cons (_, _) -> False

(** val containsEmpty : clause list -> bool **)

let rec containsEmpty = function
| Nil -> False
| Cons (c, l0) ->
  (match isEmpty c with
   | True -> True
   | False -> containsEmpty l0)

(** val rupProofCheckerUnsat : rupProof -> bool **)

let rupProofCheckerUnsat pl =
  match rupProofChecker pl with
  | True -> containsEmpty (rupProof2Conclusions pl)
  | False -> False

(** val rupProofCheckerUnsatRevFirst : rupProof -> bool **)

let rupProofCheckerUnsatRevFirst pl =
  rupProofCheckerUnsat (rev pl)

type proofStep =
| Tseitin' of clause
| Rup'0 of clause
| Assumption' of clause
| Deletion' of clause

(** val appendFor : formula -> formula -> formula **)

let rec appendFor f g =
  match f with
  | Nil -> g
  | Cons (c, f1) -> Cons (c, (appendFor f1 g))

(** val removeClauseFromFor : clause -> formula -> formula **)

let rec removeClauseFromFor c = function
| Nil -> Nil
| Cons (hd, tl) ->
  let new_formula = removeClauseFromFor c tl in
  (match clause_eqb c hd with
   | True -> new_formula
   | False -> Cons (hd, new_formula))

(** val checkProof :
    proofStep list -> formula -> (bool, proofStep option) prod **)

let rec checkProof p f =
  match p with
  | Nil -> Pair (True, None)
  | Cons (step, ps) ->
    (match step with
     | Tseitin' c -> checkProof ps (appendFor f (Cons (c, Nil)))
     | Rup'0 c ->
       (match rUP_Checker f c with
        | True -> checkProof ps (appendFor f (Cons (c, Nil)))
        | False -> Pair (False, (Some step)))
     | Assumption' a -> checkProof ps (appendFor f (Cons (a, Nil)))
     | Deletion' c -> checkProof ps (removeClauseFromFor c f))
