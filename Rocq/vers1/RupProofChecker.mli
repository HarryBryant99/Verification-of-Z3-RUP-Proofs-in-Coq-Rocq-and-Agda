
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

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

type literal =
| Pos of string
| Neg of string

val literal_eqb : literal -> literal -> bool

val negate : literal -> literal

type clause = literal list

type formula = clause list

type assumption = formula

type splitClauses = ((clause list, literal list) prod, bool) prod

type preparePropStep = ((clause list, literal list) prod, literal) prod

type splitLiterals = (literal list, bool) prod

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

val literal_in_seen : literal -> string list -> bool

val addVarsInClauseToSeen : clause -> string list -> string list

val addVarsInForToSeen : formula -> string list -> string list

val length : 'a1 list -> nat

val countVarsInFor : formula -> nat

val unitPropagationAndCheck : assumption -> bool

val clause_eqb : literal list -> literal list -> bool

val negate_clause : clause -> formula

val rUP_Checker : assumption -> clause -> bool

type rupProofStep =
| Ass' of clause
| Rup' of clause

type rupProof = rupProofStep list

val rupProof2Assumptions : rupProof -> clause list

val rupProof2AssumptionsRevFirst : rupProof -> clause list

val rupProof2Conclusions : rupProof -> clause list

val rupProof2ConclusionsRevFirst : rupProof -> clause list

val rupProofChecker : rupProof -> bool

val rupProofCheckerRevFirst : rupProof -> bool

val isEmpty : clause -> bool

val containsEmpty : clause list -> bool

val rupProofCheckerUnsat : rupProof -> bool

val rupProofCheckerUnsatRevFirst : rupProof -> bool

type proofStep =
| Tseitin' of clause
| Rup'0 of clause
| Assumption' of clause
| Deletion' of clause

val appendFor : formula -> formula -> formula

val removeClauseFromFor : clause -> formula -> formula

val checkProof : proofStep list -> formula -> (bool, proofStep option) prod
