
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

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

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

type clause = literal list

type formula = clause list

type assumption = formula

val literal_eqb : literal -> literal -> bool

val negate : literal -> literal

val negate_clause : clause -> formula

val removeLitFromClause : literal -> clause -> clause

val lit_in_clause : literal -> clause -> bool

val literal_in_seen : literal -> string list -> bool

val addVarsInClauseToSeen : clause -> string list -> string list

val addVarsInForToSeen : formula -> string list -> string list

val countVarsInFor : formula -> nat

type splitClauses = ((clause list, literal list) prod, bool) prod

type splitLiterals = (literal list, bool) prod

type preparePropStep = ((clause list, literal list) prod, literal) prod

val splitClauses_to_bool : splitClauses -> bool

val addClauseToSplitClauses : clause -> splitClauses -> splitClauses

val splitClauses0 : clause list -> splitClauses

val processOneClause_aux2 : clause -> literal -> bool -> clause

val processOneClause_aux1 : clause -> literal -> bool -> clause option

val processOneClause : clause -> literal -> clause option

val processClausesaux : clause option -> clause list -> clause list

val processClauses : clause list -> literal -> clause list

val processAndSplitClausesWithLit : clause list -> literal -> splitClauses

val combineSplitClausesSplitLits :
  splitClauses -> splitLiterals -> splitClauses

val processListLitsWithLit : literal list -> literal -> splitLiterals

val propagationStep' : clause list -> literal list -> literal -> splitClauses

val propagationStep : preparePropStep -> splitClauses

val selectAndRunPropagator :
  splitClauses -> (splitClauses -> splitClauses) -> splitClauses

val iteratePropagator : nat -> splitClauses -> splitClauses

val unitPropagationAndCheck : assumption -> bool

val rUP_Checker : assumption -> clause -> bool

type proofStep =
| Tseitin of clause
| Rup of clause
| Assumption of clause
| Deletion of clause

type preProof = proofStep list

val clause_eqb : literal list -> literal list -> bool

val remove_clause : clause -> formula -> formula

val checkProof : preProof -> formula -> (bool, proofStep option) prod
