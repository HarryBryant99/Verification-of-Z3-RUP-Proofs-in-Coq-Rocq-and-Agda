
type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

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

val false_string : char list

val falseFor : z3_Formula

val negFor : z3_Formula -> z3_Formula

val andFor : zClause -> z3_Formula

val orFor : zClause -> z3_Formula

val nthWithDefault : nat -> zClause -> z3_Formula -> z3_Formula

val negForList : zClause -> zClause

val tseitinNot2For : z3_Formula -> zClause

val tseitinImpElim2For : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro1toFor : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro2toFor : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro3toFor : z3_Formula -> z3_Formula -> zClause

val tseitinAndIntro2ForOpt : zClause -> zClause

val tseitinAndElim2For : zClause -> nat -> zClause

val tseitinOrIntro2For : zClause -> nat -> zClause

val tseitinOrElim2ForOpt : zClause -> zClause

val tseitinProofItem2ConclusionOpt : tseitinStep -> zClause

val zProofItem2ConclusionOpt : zProofItem -> zClause

val length_listZ3 : zClause -> nat

val z3_formula_eq : z3_Formula -> z3_Formula -> bool

val list_z3_formula_eq : listZ3_Formula -> listZ3_Formula -> bool

val pos_z3_formula_eq : pos_Z3_Formula -> pos_Z3_Formula -> bool

val literal_eqb : literal -> literal -> bool

val negate : literal -> literal

type assumption = clause list

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

val zfor2Lit : z3_Formula -> literal

val zCl2RClause : zClause -> clause

val zListCl2RListCl : zClause list -> clause list

val zProof2ConclusionOpt : zProof -> zClause list

val in_listZ3b : z3_Formula -> listZ3_Formula -> bool

val listZ3_subset : listZ3_Formula -> listZ3_Formula -> bool

val negSingletons : listZ3_Formula -> listZ3_Formula list

val in_listZ3List : listZ3_Formula -> listZ3_Formula list -> bool

val listZ3List_subset : listZ3_Formula list -> listZ3_Formula list -> bool

val setminus : listZ3_Formula -> listZ3_Formula -> listZ3_Formula

val zProofCheckTseitin : tseitinStep -> bool

val zProofCheckLastStep : zClause list -> zProofItem -> bool

val zProofCheck : zProof -> bool

  type zProofCheckResult =
  | Passed
  | Failed of zProofItem

val zProofCheckWithFailure : zProof -> zProofCheckResult
