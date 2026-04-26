
val negb : bool -> bool

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

module Nat :
 sig
  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val min : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val geb : int -> int -> bool
 end

val list_length : 'a1 list -> int

type z3_Variable_Bool = int

type z3_Variable_Int = int

type listIntExpr = (z3_Variable_Int * int list) list

type linIntExpr = (z3_Variable_Int * int) list

type linIntExprWithRHS = { vars : linIntExpr; int : int }

type farkasFormulas = { lhs : listIntExpr; rhs : int list }

type farkasStep = { mults : int list; constrs : farkasFormulas }

type z3_Equality = { eq_vars : linIntExpr; eq_int : int }

type z3_Formula =
| Z3var of z3_Variable_Bool
| Z3eq of z3_Equality
| Z3ineq of linIntExprWithRHS
| And of listZ3_Formula
| Or of listZ3_Formula
| Imply of z3_Formula * z3_Formula
| Not of z3_Formula
and listZ3_Formula =
| Lnil
| Lcons of z3_Formula * listZ3_Formula

type pos_Z3_Formula =
| Pos_z3var of z3_Variable_Bool
| Pos_z3eq of z3_Equality
| Pos_z3ineq of linIntExprWithRHS
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
| TseitinAndElim of listZ3_Formula * int
| TseitinOrIntro of listZ3_Formula * int
| TseitinOrElim of listZ3_Formula

type zProofItem =
| TseitinStep of tseitinStep
| AssumptionZ3 of listZ3_Formula
| RupZ3proof of listZ3_Formula
| TseitinStepRed of tseitinStep * listZ3_Formula
| Deletion of listZ3_Formula
| Farkas of farkasStep

type zClause = listZ3_Formula

val false_string : int

val falseFor : z3_Formula

val negFor : z3_Formula -> z3_Formula

val andFor : zClause -> z3_Formula

val orFor : zClause -> z3_Formula

val nthWithDefault : int -> zClause -> z3_Formula -> z3_Formula

val negForList : zClause -> zClause

val tseitinNot2For : z3_Formula -> zClause

val tseitinImpElim2For : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro1toFor : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro2toFor : z3_Formula -> z3_Formula -> zClause

val tseitinImpIntro3toFor : z3_Formula -> z3_Formula -> zClause

val tseitinAndIntro2ForOpt : zClause -> zClause

val tseitinAndElim2For : zClause -> int -> zClause

val tseitinOrIntro2For : zClause -> int -> zClause

val tseitinOrElim2ForOpt : zClause -> zClause

val tseitinProofItem2ConclusionOpt : tseitinStep -> zClause

val pair_head_int_list_prime :
  z3_Variable_Int -> int list -> z3_Variable_Int * int

val pair_to_first_row : listIntExpr -> linIntExpr

val pair_tail_int_list_prime :
  z3_Variable_Int -> int list -> z3_Variable_Int * int list

val pair_to_tail : listIntExpr -> listIntExpr

val pair_matrix_to_first_k_rows : listIntExpr -> int -> linIntExpr list

val pair_list_min_aux : listIntExpr -> int

val pair_matrix_to_rows : listIntExpr -> linIntExpr list

val nonzero_coeff : (z3_Variable_Int * int) -> bool

val prune_linexpr : linIntExpr -> linIntExpr

val lin_rows_with_rhs_aux :
  linIntExpr list -> int list -> linIntExprWithRHS list

val lin_rows_with_rhs : farkasFormulas -> linIntExprWithRHS list

val negate_lin_rows : linIntExprWithRHS list -> listZ3_Formula

val farkas_step_to_clause : farkasStep -> listZ3_Formula

val zProofItem2ConclusionOpt : zProofItem -> zClause

val length_listZ3 : zClause -> int

val z3_Variable_Int_eqb : z3_Variable_Int -> z3_Variable_Int -> bool

val pair_int_expr_eqb :
  (z3_Variable_Int * int) -> (z3_Variable_Int * int) -> bool

val linIntExpr_eqb : linIntExpr -> linIntExpr -> bool

val linIntExprWithRHS_eqb : linIntExprWithRHS -> linIntExprWithRHS -> bool

val z3_Equality_eqb : z3_Equality -> z3_Equality -> bool

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

val iteratePropagator : int -> splitClauses -> splitClauses

val splitClauses_to_bool : splitClauses -> bool

val literal_in_seen : literal -> pos_Z3_Formula list -> bool

val addVarsInClauseToSeen :
  clause -> pos_Z3_Formula list -> pos_Z3_Formula list

val addVarsInForToSeen : formula -> pos_Z3_Formula list -> pos_Z3_Formula list

val countVarsInFor : formula -> int

val unitPropagationAndCheck : assumption -> bool

val negate_clause : clause -> formula

val rUP_Checker : assumption -> clause -> bool

val scale_Integers : int list -> int list -> int list

val scale1Column :
  int list -> (z3_Variable_Int * int list) -> z3_Variable_Int * int list

val scaleColumns : int list -> listIntExpr -> listIntExpr

val add_Column : int list -> int

val add_Column_Pair : (z3_Variable_Int * int list) -> z3_Variable_Int * int

val add_ListIntExpr : listIntExpr -> linIntExpr

val add_RHS : int list -> int

val scale_and_add_LHS : int list -> listIntExpr -> linIntExpr

val scale_and_add_RHS : int list -> int list -> int

val lhs_equals_zero : linIntExpr -> bool

val lHS_zero_after_scaling : int list -> listIntExpr -> bool

val rHS_value_after_scaling : int list -> int list -> int

val ge_Z : int -> int -> bool

val ge0b : int -> bool

val ms_nonnegb : int list -> bool

val rows_rhs_len_eqb : farkasFormulas -> bool

val multiplier_check : int list -> farkasFormulas -> bool

val farkas_contradiction : farkasStep -> bool

val zfor2Lit : z3_Formula -> literal

val zCl2RClause : zClause -> clause

val zListCl2RListCl : zClause list -> clause list

val remove_listZ3_Formula :
  listZ3_Formula -> listZ3_Formula list -> listZ3_Formula list

val in_listZ3b : z3_Formula -> listZ3_Formula -> bool

val listZ3_subset : listZ3_Formula -> listZ3_Formula -> bool

val negSingletons : listZ3_Formula -> listZ3_Formula list

val in_listZ3List : listZ3_Formula -> listZ3_Formula list -> bool

val listZ3List_subset : listZ3_Formula list -> listZ3_Formula list -> bool

val setminus : listZ3_Formula -> listZ3_Formula -> listZ3_Formula

val subset_in_list : listZ3_Formula -> listZ3_Formula list -> bool

val zProofCheckTseitin : tseitinStep -> bool

val zProofCheckLastStep : zClause list -> zProofItem -> bool

val zProof2ConclusionOptPrime : zClause list -> zProofItem -> zClause list

val checkList :
  zClause list -> zClause list -> zProofItem list -> bool -> (zClause
  list * zClause list) * bool

val checkList_trim :
  zClause list -> zProofItem list -> bool -> zClause list * bool
