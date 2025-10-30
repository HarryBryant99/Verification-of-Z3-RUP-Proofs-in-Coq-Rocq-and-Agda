
type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val eqb : char list -> char list -> bool

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

type assumption = formula

val z3_formula_eq : z3_Formula -> z3_Formula -> bool

val list_z3_formula_eq : listZ3_Formula -> listZ3_Formula -> bool

val pos_z3_formula_eq : pos_Z3_Formula -> pos_Z3_Formula -> bool

val literal_eqb : literal -> literal -> bool

val negate : literal -> literal

type splitClauses = (clause list * literal list) * bool

type preparePropStep = (clause list * literal list) * literal

type splitLiterals = literal list * bool

val removeLitFromClause : literal -> clause -> clause

val lit_in_clause : literal -> clause -> bool

val processOneClause_aux2 : clause -> literal -> bool -> clause

val processOneClause_aux1 : clause -> literal -> bool -> clause option

val processOneClause : clause -> literal -> clause option

val processClausesaux : clause option -> clause list -> clause list

val processClauses : clause list -> literal -> clause list

val addClauseToSplitClauses : clause -> splitClauses -> splitClauses

val splitClauses0 : clause list -> splitClauses

val processAndSplitClausesWithLit : clause list -> literal -> splitClauses

val processListLitsWithLit : literal list -> literal -> splitLiterals

val combineSplitClausesSplitLits :
  splitClauses -> splitLiterals -> splitClauses

val propagationStep' : clause list -> literal list -> literal -> splitClauses

val propagationStep : preparePropStep -> splitClauses

val selectAndRunPropagator :
  splitClauses -> (splitClauses -> splitClauses) -> splitClauses

val iteratePropagator : nat -> splitClauses -> splitClauses

val splitClauses_to_bool : splitClauses -> bool

val literal_in_seen : literal -> pos_Z3_Formula list -> bool

val addVarsInClauseToSeen :
  clause -> pos_Z3_Formula list -> pos_Z3_Formula list

val addVarsInForToSeen : formula -> pos_Z3_Formula list -> pos_Z3_Formula list

val length : 'a1 list -> nat

val countVarsInFor : formula -> nat

val unitPropagationAndCheck : assumption -> bool

val negate_clause : clause -> formula

val rUP_Checker : assumption -> clause -> bool

type proofStep =
| Tseitin of (clause * clause)
| Rup of clause
| Assumption of clause
| Deletion of clause

type preProof = proofStep list

val clause_eqb : literal list -> literal list -> bool

val remove_clause : clause -> formula -> formula

(*
val checkProof : preProof -> formula -> bool * proofStep option
*)