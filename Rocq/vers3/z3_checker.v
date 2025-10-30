(*--------------------------------------------------------------------------*)

(* Importing necessary libraries *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.Arith.Arith.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import Coq.Sorting.Permutation.

(*--------------------------------------------------------------------------*)

(* Datatypes *)

Definition Z3_Variable := string.

Inductive Z3_Formula : Type :=
| z3var : Z3_Variable -> Z3_Formula
| and : listZ3_Formula -> Z3_Formula
| or : listZ3_Formula -> Z3_Formula
| imply : Z3_Formula -> Z3_Formula -> Z3_Formula
| not : Z3_Formula -> Z3_Formula

with listZ3_Formula : Type :=
| lnil : listZ3_Formula
| lcons : Z3_Formula -> listZ3_Formula -> listZ3_Formula.

Inductive Pos_Z3_Formula : Type :=
| pos_z3var : Z3_Variable -> Pos_Z3_Formula
| pos_and : listZ3_Formula -> Pos_Z3_Formula
| pos_or : listZ3_Formula -> Pos_Z3_Formula
| pos_imply : Z3_Formula -> Z3_Formula -> Pos_Z3_Formula.

Inductive Literal : Type :=
| pos : Pos_Z3_Formula -> Literal
| neg : Pos_Z3_Formula -> Literal.

Definition Clause := list Literal.
Definition Formula := list Clause.

Inductive TseitinStep : Type :=
| tseitinNot : Z3_Formula -> TseitinStep
| tseitinImpElim : Z3_Formula -> Z3_Formula -> TseitinStep
| tseitinImpIntro1 : Z3_Formula -> Z3_Formula -> TseitinStep
| tseitinImpIntro2 : Z3_Formula -> Z3_Formula -> TseitinStep
| tseitinImpIntro3 : Z3_Formula -> Z3_Formula -> TseitinStep
| tseitinAndIntro : listZ3_Formula -> TseitinStep
| tseitinAndElim : listZ3_Formula -> nat -> TseitinStep
| tseitinOrIntro : listZ3_Formula -> nat -> TseitinStep
| tseitinOrElim : listZ3_Formula -> TseitinStep.

Inductive ZProofItem : Type :=
| tseitinStep : TseitinStep -> ZProofItem
| assumptionZ3 : listZ3_Formula -> ZProofItem
| rupZ3proof : listZ3_Formula -> ZProofItem
| tseitinStepRed : TseitinStep -> listZ3_Formula -> ZProofItem.

Definition ZProof := list ZProofItem.

(*
Definition ZClause := list Z3_Formula.
*)
Definition ZClause := listZ3_Formula.

Definition true_string : string := "TRUE".
Definition false_string : string := "FALSE".

Definition falseFor : Z3_Formula := z3var false_string.

(*--------------------------------------------------------------------------*)

(* Define model as a function type from atom to bool *)
Definition Model := Pos_Z3_Formula -> bool.

Definition models_literal (m : Model) (l : Literal) : bool :=
  match l with
  | pos x => m x
  | neg x => negb (m x)
  end.

Fixpoint models_clause (m : Model) (c : Clause) : bool :=
  match c with
  | [] => false
  | h :: t => orb (models_literal m h) (models_clause m t)
  end.

Fixpoint models_formula (m : Model) (f : Formula) : bool :=
  match f with
  | [] => true
  | h :: t => andb (models_clause m h) (models_formula m t)
  end.

(* Define the function IsTrue *)
Definition IsTrue (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

Definition Models_literal (m : Model) (l : Literal) : Prop :=
  IsTrue (models_literal m l).

Definition Models_clause (m : Model) (c : Clause) : Prop :=
  IsTrue (models_clause m c).

Definition Models_formula (m : Model) (f : Formula) : Prop :=
  IsTrue (models_formula m f).

(*--------------------------------------------------------------------------*)

Definition negFor (f : Z3_Formula) : Z3_Formula :=
  match f with
  | not x => x
  | z3var v => not f
  | _ => not f
  end.

Fixpoint flatten_listZ3 (l : ZClause) : list Z3_Formula  :=
  match l with
  | lnil => []
  | lcons x xs => x :: flatten_listZ3 xs
  end.

Definition andFor (l : ZClause) : Z3_Formula :=
  and l.

Definition orFor (l : ZClause) : Z3_Formula :=
  or l.

Fixpoint nthWithDefault (n : nat) (l : ZClause) (default : Z3_Formula) : Z3_Formula :=
  match n, l with
  | O, lcons x _ => x
  | S n', lcons _ xs => nthWithDefault n' xs default
  | _, _ => default
  end.

Fixpoint append_listZ3 (l1 l2 : ZClause) : ZClause :=
  match l1 with
  | lnil => l2
  | lcons x xs => lcons x (append_listZ3 xs l2)
  end.

Fixpoint negForList (l : ZClause) : ZClause :=
  match l with
  | lnil => lnil
  | lcons a rest => lcons (negFor a) (negForList rest)
  end.

(* NOT transformation *)
Definition tseitinNot2For (a : Z3_Formula) : ZClause :=
  lcons a (lcons (negFor a) lnil).

(* Implication elimination *)
Definition tseitinImpElim2For (a b : Z3_Formula) : ZClause :=
  lcons (negFor a) (lcons b (lcons (not (imply a b)) lnil)).

(* Implication introduction variants *)
Definition tseitinImpIntro1toFor (a b : Z3_Formula) : ZClause :=
  lcons a (lcons (imply a b) lnil).

Definition tseitinImpIntro2toFor (a b : Z3_Formula) : ZClause :=
  lcons (negFor b) (lcons (imply a b) lnil).

Definition tseitinImpIntro3toFor (a b : Z3_Formula) : ZClause :=
  lcons (not b) (lcons (imply a b) lnil).

(* AND introduction *)
Definition tseitinAndIntro2ForOriginal (l : ZClause) : ZClause :=
  append_listZ3 (negForList l) (lcons (andFor l) lnil).

Definition tseitinAndIntro2ForOpt (l : ZClause) : ZClause :=
  lcons (andFor l) (negForList l).

(* AND elimination *)
Definition tseitinAndElim2For (l : ZClause) (i : nat) : ZClause :=
  lcons (nthWithDefault i l falseFor) (lcons (not (andFor l)) lnil).

(* OR introduction *)
Definition tseitinOrIntro2For (l : ZClause) (i : nat) : ZClause :=
  lcons (negFor (nthWithDefault i l falseFor)) (lcons (orFor l) lnil).

(* OR elimination *)
Definition tseitinOrElim2ForOriginal (l : ZClause) : ZClause :=
  append_listZ3 l (lcons (not (orFor l)) lnil).

Definition tseitinOrElim2ForOpt (l : ZClause) : ZClause :=
  lcons (not (orFor l)) l.


(*--------------------------------------------------------------------------*)

Fixpoint ZProof2Assumption (p : ZProof) : list (ZClause) :=
  match p with
  | [] => []
  | assumptionZ3 x :: rest => x :: ZProof2Assumption rest
  | _ :: rest => ZProof2Assumption rest
  end.

Definition TseitinProofItem2ConclusionOpt (item : TseitinStep) : ZClause :=
  match item with
  | tseitinNot a => tseitinNot2For a
  | tseitinImpElim a b => tseitinImpElim2For a b
  | tseitinImpIntro1 a b => tseitinImpIntro1toFor a b
  | tseitinImpIntro2 a b => tseitinImpIntro2toFor a b
  | tseitinImpIntro3 a b => tseitinImpIntro3toFor a b
  | tseitinAndIntro l => tseitinAndIntro2ForOpt l
  | tseitinAndElim l i => tseitinAndElim2For l i
  | tseitinOrIntro l i => tseitinOrIntro2For l i
  | tseitinOrElim l => tseitinOrElim2ForOpt l
  end.

Definition ZProofItem2ConclusionOpt (item : ZProofItem) : ZClause :=
  match item with
  | tseitinStep a => TseitinProofItem2ConclusionOpt a
  | assumptionZ3 a => a
  | rupZ3proof a => a
  | tseitinStepRed a c => c
  end.

Fixpoint length_listZ3 (l : ZClause) : nat :=
  match l with
  | lnil => 0
  | lcons _ rest => S (length_listZ3 rest)
  end.

(*--------------------------------------------------------------------------*)
(*RUP Proof*)

Definition defaultLiteral_string : string := "defaultLiteral".
Definition defaultLiteral : Literal := pos (pos_z3var defaultLiteral_string).

Fixpoint z3_formula_eq (f1 f2 : Z3_Formula) : bool :=
  match f1, f2 with
  | z3var x, z3var y => String.eqb x y
  | and l1, and l2 => list_z3_formula_eq l1 l2
  | or l1, or l2 => list_z3_formula_eq l1 l2
  | imply a1 b1, imply a2 b2 => z3_formula_eq a1 a2 && z3_formula_eq b1 b2
  | not f1', not f2' => z3_formula_eq f1' f2'
  | _, _ => false
  end

with list_z3_formula_eq (l1 l2 : listZ3_Formula) : bool :=
  match l1, l2 with
  | lnil, lnil => true
  | lcons h1 t1, lcons h2 t2 =>
      z3_formula_eq h1 h2 && list_z3_formula_eq t1 t2
  | _, _ => false
  end.

Definition pos_z3_formula_eq (p1 p2 : Pos_Z3_Formula) : bool :=
  match p1, p2 with
  | pos_z3var x, pos_z3var y => String.eqb x y
  | pos_and l1, pos_and l2
  | pos_or l1, pos_or l2 => list_z3_formula_eq l1 l2
  | pos_imply l1 l2, pos_imply l3 l4 => z3_formula_eq l1 l3 && z3_formula_eq l2 l4
  | _, _ => false
  end.

Definition literal_eqb (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | pos p1, pos p2 => pos_z3_formula_eq p1 p2
  | neg p1, neg p2 => pos_z3_formula_eq p1 p2
  | _, _ => false
  end.


Definition negate (b : Literal) : Literal :=
  match b with
  | pos x => neg x
  | neg x => pos x
  end.

Definition Assumption := list Clause.

Definition entails (f : Formula) (c : Clause) : Prop :=
  (forall (m : Model),
    Models_formula m f -> Models_clause m c).

Definition BooltoOC (b : bool) : option Clause :=
match b with
| true => Some []
| _ => None
end.

Definition OptionClauseToClause (otp : option Clause) : Clause :=
  match otp with
  | None => []
  | Some c => c
  end.

Definition OptionClauseToBool (oc : option Clause) : bool :=
match oc with
| Some c => true
| _ => false
end.

Inductive TreeProof : Type :=
  | ass : nat -> TreeProof
  | ures : TreeProof -> TreeProof -> TreeProof.

Definition SplitClauses : Type := (list Clause * list Literal * bool).
Definition SplitTreeProofs : Type := (list TreeProof * list TreeProof * option TreeProof).
(* default element of SplitTreeProofs
   to be used if we are in a situation which when correct should never occur
   but need to provide an element of PreparePropStepProofs   *)
Definition defaulSplitTreeProofs : SplitTreeProofs :=  ([],[],None).

(* the input for one step propagation, where we have a list of clauses,
  list of literals and a selected literal to process the list of clauses and literals *)
Definition PreparePropStep : Type := (list Clause * list Literal * Literal).

(* proofs for PreparePropStep *)
Definition PreparePropStepProofs : Type := (list TreeProof * list TreeProof * TreeProof).

(* default element of PreparePropStepProofs
   to be used if we are in a situation which when correct should never occur
   but need to provide an element of PreparePropStepProofs  *)
Definition defaultPreparePropStepProofs : PreparePropStepProofs :=
          ([],[],ass 0).

(* was RemovedLiteral *)
Definition SplitLiterals : Type := (list Literal * bool).

Definition SplitLiteralsProof : Type := (list TreeProof * option TreeProof).

(*--------------------------------------------------------------------------*)

(* Auxiliary function to remove a Literal from a Clause *)
Fixpoint removeLitFromClause (l : Literal) (c : Clause) : Clause :=
  match c with
  | [] => []
  | hd :: tl =>
      let new_clause := removeLitFromClause l tl in
      if literal_eqb l hd then new_clause
      else hd :: new_clause
  end.

(* Return an element from a list of Assumptions *)
Definition findAssumption (ass : Assumption) (i : nat) : option Clause :=
  nth_error ass i .

Definition correctConclusionRes (c1 : option Clause)(c2 : option Clause) : option Clause :=
      match c1 with
      | None => None
      | Some c1 => match c2 with
                   |None => None
                   |Some [ l ] => Some (removeLitFromClause (negate l) c1)
                   |Some _     => None
                   end
      end .

Definition ClauseToLiteralWithDefault (c : Clause) : Literal :=
match c with
| [] => defaultLiteral
| (l :: ls) => l
end.

Lemma ClauseToLiteralWithDefaultCorrect :
forall (l : Literal),
  ClauseToLiteralWithDefault [l] = l.
Proof.
intros.
simpl. reflexivity.
Qed.

(* Define a helper function to check if a clause is a unit clause *)
Definition is_unit_clause (c : Clause) : bool :=
  match c with
  | [] => false
  | [_] => true
  | _ => false
  end.

Lemma UnitClauseCorrect :
forall (c : Clause),
  is_unit_clause c = true ->
  c = [ClauseToLiteralWithDefault c].
Proof.
intros.
destruct c.
simpl in *. discriminate.
simpl in *.
destruct c.
reflexivity.
discriminate.
Qed.

Lemma correctConclusionResTrue1 :
forall (c1 c2 : option Clause),
  OptionClauseToBool (correctConclusionRes c1 c2) = true ->
  OptionClauseToBool c1 = true.
Proof.
intros.
destruct c1.
+
destruct c2.
- simpl. reflexivity.
- simpl. reflexivity.
+
destruct c2.
- discriminate.
- discriminate.
Qed.

Lemma correctConclusionResTrue2 :
forall (c1 c2 : option Clause),
  OptionClauseToBool (correctConclusionRes c1 c2) = true ->
  OptionClauseToBool c2 = true.
Proof.
intros.
destruct c1.
+
destruct c2.
- simpl. reflexivity.
- simpl. discriminate.
+
destruct c2.
- discriminate.
- discriminate.
Qed.

Lemma correctConclusionResToUnitClauseTrue :
forall (c1 c2 : option Clause),
  OptionClauseToBool (correctConclusionRes c1 c2) = true ->
  is_unit_clause (OptionClauseToClause c2) = true.
Proof.
intros.
destruct c1.
+ destruct c2.
  destruct c0.
  simpl in *. discriminate.
  simpl in *.
  destruct c0.
  reflexivity.
  discriminate.
  discriminate.
+ destruct c2.
  discriminate.
  discriminate.
Qed.

Lemma correctConclusionResTrue :
forall (c1 c2 : option Clause) (c : Clause),
  correctConclusionRes c1 c2 = Some c ->
  c =
     (removeLitFromClause
     (negate (ClauseToLiteralWithDefault (OptionClauseToClause c2))) (OptionClauseToClause c1)).
Proof.
intros.
destruct c1.
+ destruct c2.
  destruct c1.
  - simpl in *.
    discriminate.
  - simpl in *.
    destruct c1.
    injection H as H1.
    symmetry.
    assumption.
    discriminate.
  - discriminate.
+ destruct c2.
  simpl in *.
  - discriminate.
  - discriminate.
Qed.

(* Define the correctConclusion function *)
Fixpoint correctConclusion (al : Assumption) (t : TreeProof) : option Clause :=
  match t with
  | ass n => findAssumption al n
  | ures t1 t2 => correctConclusionRes (correctConclusion al t1) (correctConclusion al t2)
  end.

Fixpoint correctConclusions (al : Assumption) (ts : list TreeProof) : list Clause :=
  match ts with
  | [] => []
  | t :: ts' =>
      match correctConclusion al t with
      | Some c => c :: correctConclusions al ts'
      | None => correctConclusions al ts'
      end
  end.

(*--------------------------------------------------------------------------*)

(* Proof Definitions to show the relation between the levels *)

Definition CorrectProof (al : Assumption)(c : Clause)(t : TreeProof) : Prop :=
  correctConclusion al t = Some c .

Definition CorrectOptionProof (al : Assumption)(c : option Clause)
(t : option TreeProof) : Prop :=
  match c with
  | None => match t with
              | None => True
              | Some t => False
              end
  | Some c => match t with
              | None => False
              | Some t => CorrectProof al c t
              end
  end.

Fixpoint CorrectProofList (al : Assumption)(c : list Clause)(t : list TreeProof) : Prop :=
  match c with
  | [] =>
      match t with
      |  [] => True
      |  _  => False
      end
  | (c :: cl) => match t with
                 | [] => False (* not enough tree proofs *)
                 | (cp :: clp) => CorrectProof al c cp /\
                                    CorrectProofList al cl clp
                 end
  end.

Definition CorrectOptionTreeProof (al : Assumption)(b : bool)(t : option TreeProof) : Prop :=
  CorrectOptionProof al (BooltoOC b) t.

Definition CorrectOptionTreeProof' (al : Assumption)(b : bool)(t : option TreeProof) : Prop :=
  match b with
  | false =>
      match t with
      |  None => True
      |  _  => False
      end
  | true => match t with
                 | None => False (* not enough tree proofs *)
                 | Some t => CorrectProof al [] t
                 end
  end.

Lemma CorrectOpenTreeProofEquiv1 :
  forall (al : Assumption)(b : bool)(t : option TreeProof),
    CorrectOptionTreeProof' al b t
    -> CorrectOptionTreeProof al b t.
Proof.
  intros.
  destruct b.
  destruct t.
  unfold CorrectOptionTreeProof' in H.
  unfold CorrectOptionTreeProof.
  unfold BooltoOC.
  unfold CorrectOptionProof.
  assumption.
  unfold CorrectOptionTreeProof' in H.
  contradiction.
  destruct t.
  unfold CorrectOptionTreeProof' in H.
  contradiction.
  unfold CorrectOptionTreeProof' in H.
  unfold CorrectOptionTreeProof.
  unfold BooltoOC.
  unfold CorrectOptionProof.
  assumption.
Qed.


Lemma CorrectOpenTreeProofEquiv2 :
  forall (al : Assumption)(b : bool)(t : option TreeProof),
    CorrectOptionTreeProof al b t
    -> CorrectOptionTreeProof' al b t.
Proof.
  intros.
  destruct b.
  destruct t.
  unfold CorrectOptionTreeProof in H.
  unfold CorrectOptionTreeProof'.
  unfold BooltoOC in H.
  unfold CorrectOptionProof in H.
  assumption.
  unfold CorrectOptionTreeProof in H.
  unfold BooltoOC in H.
  unfold CorrectOptionProof in H.
  contradiction.
  destruct t.
  unfold CorrectOptionTreeProof in H.
  unfold BooltoOC in H.
  unfold CorrectOptionProof in H.
  contradiction.
  unfold CorrectOptionTreeProof in H.
  unfold CorrectOptionTreeProof'.
  unfold BooltoOC in H.
  unfold CorrectOptionProof in H.
  assumption.
Qed.


Fixpoint CorrectLiteralProof (al : Assumption)(l : list Literal)
(t : list TreeProof) : Prop :=
  match l with
  | [] =>
      match t with
      |  [] => True
      |  _  => False
      end
  | (l :: ls) => match t with
              | [] => False
              | (t :: ts) => CorrectProof al [l] t /\
                             CorrectLiteralProof al ls ts
              end
  end.

Lemma CorrectLiteralProofUnfold1 :
  forall (al : Assumption)(l : Literal)(ls : list Literal)
         (lp : TreeProof) (lsp : list TreeProof),
    CorrectLiteralProof al (l :: ls) (lp :: lsp)
    -> CorrectProof al [l] lp /\ CorrectLiteralProof al ls lsp.
Proof.
  intros.
  apply H.
Qed.

Lemma CorrectLiteralProofUnfold2 :
  forall (al : Assumption)(l : Literal)(ls : list Literal)
         (lp : TreeProof) (lsp : list TreeProof),
    CorrectProof al [l] lp /\ CorrectLiteralProof al ls lsp
    -> CorrectLiteralProof al (l :: ls) (lp :: lsp).
Proof.
  intros.
  apply H.
Qed.


Definition CorrectSplit (al : Assumption)(c : SplitClauses)(t : SplitTreeProofs) : Prop :=
  match c with
  | (clauses,literals,b) =>
      match t with
      | (ct,lt,bt) => (CorrectProofList al clauses ct) /\
                      (CorrectLiteralProof al literals lt) /\
                      (CorrectOptionTreeProof' al b bt)
      end
  end.

Definition CorrectSplitLiterals (al : Assumption)(l : SplitLiterals)(t : SplitLiteralsProof) : Prop :=
  match l with
  | (literals,b) =>
      match t with
      | (lt,bt) => (CorrectLiteralProof al literals lt) /\
                   (CorrectOptionTreeProof' al b bt)
      end
  end.


Definition CorrectPreparePropStep (al : Assumption)(p : PreparePropStep)(pt : PreparePropStepProofs) : Prop :=
  match p with
  | (cs,ls,l) =>
      match pt with
      | (ct,lst,lt) =>
          (CorrectProofList al cs ct)
          /\ (CorrectLiteralProof al ls lst)
          /\ (CorrectProof al [l] lt)
      end
  end.


Lemma Resolution_Correct :
  forall (al : Assumption)(l : Literal)(c : Clause)(lp : TreeProof) (cp : TreeProof),
    CorrectProof al [l] lp /\   CorrectProof al c cp
    ->  CorrectProof al   (removeLitFromClause (negate l) c)
          (ures cp lp).
Proof .
  intros .
  destruct H as [H1  H2] .
  unfold CorrectProof in H1.
  unfold CorrectProof  in H1.
  unfold CorrectProof in H2.
  unfold CorrectProof .
  replace (correctConclusion al (ures cp lp)) with (correctConclusionRes (correctConclusion al cp) (correctConclusion al lp)) .
  replace (correctConclusion al lp) with (Some [l]).
  replace (correctConclusion al cp) with (Some c) .
  replace (correctConclusionRes (Some c) (Some [l])) with (Some (removeLitFromClause (negate l) c)).
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(*--------------------------------------------------------------------------*)

Definition lit_in_clause (l : Literal)(c : Clause) : bool :=
  existsb (literal_eqb l) c .

(*--------------------------------------------------------------------------*)

(* processOneClause_aux2 assumes that b is the test whether negate l
                         occurs in c
   if it does it removes from c (oppsite l), otherwise
   it returns c as is *)
Definition processOneClause_aux2 (c : Clause)(l : Literal) (b : bool) : Clause :=
  match b with
  | false =>  c   (* neither l nor ¬l in clause, just keep it *)
  | true  =>  removeLitFromClause (negate l) c
  end .

Definition processOneClause_aux2_proof (c : Clause)(l : Literal)(b : bool)
  (cp : TreeProof)(lp : TreeProof)  :=
  match b with
  | false =>  cp
  | true  =>  ures cp lp
  end .

Lemma processOneClause_aux2_correct : forall (as0 : Assumption)
                                             (c : Clause)(l : Literal)
                                             (b : bool)
                                         (cp : TreeProof) (lp : TreeProof),

    CorrectProof as0 c cp /\ CorrectProof as0 [ l ]  lp
    -> CorrectProof as0 (processOneClause_aux2 c l b) (processOneClause_aux2_proof c l b cp lp).
Proof .
 intros .
 destruct H as [H1  H2] .
 destruct b.
 unfold processOneClause_aux2 .
 unfold processOneClause_aux2_proof .
 unfold CorrectProof .
 unfold correctConclusion .
 apply Resolution_Correct.
 split .
 assumption .
 assumption .
 unfold processOneClause_aux2 .
 unfold processOneClause_aux2_proof .
 assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* processOneClause_aux1 assumes b is a test whether l occurs in c
   if it occurs it returns None
   otherwise it removes (negate l) from c and returns the result (as Some)
*)
Definition processOneClause_aux1 (c : Clause)(l : Literal) (b : bool) : option Clause :=
  match b with
    | true => None (* omit the clause
                   processOneClause_checkomit will be set to true
                   but we need to return a clause so we take just the clause
                   we have *)
    | false =>  Some (processOneClause_aux2 c l (lit_in_clause (negate l) c))
end.

Definition processOneClause_aux1_proof (c : Clause)(l : Literal)(b : bool)
  (cp : TreeProof)(lp : TreeProof)  :=
  match b with
  | true => None (* use the tree proof we have which is a proof of the
                    unnecessary clause *)
  | false => Some(processOneClause_aux2_proof c l (lit_in_clause (negate l) c)
                                         cp lp)
end.

Lemma processOneClause_aux1_correct : forall (as0 : Assumption)
                                             (c : Clause)(l : Literal)
                                             (b : bool)
                                         (cp : TreeProof) (lp : TreeProof),

    CorrectProof as0 c cp /\ CorrectProof as0 [ l ]  lp
    -> CorrectOptionProof as0 (processOneClause_aux1 c l b) (processOneClause_aux1_proof c l b cp lp).
Proof .
intros .
destruct b .
unfold processOneClause_aux1 .
unfold processOneClause_aux1_proof .
destruct H as [H1  H2] .
simpl. trivial.
unfold processOneClause_aux1 .
unfold processOneClause_aux1_proof .
apply processOneClause_aux2_correct .
destruct H as [H1  H2] .
split .
assumption .
assumption .
Qed.

(*--------------------------------------------------------------------------*)

(* processOneClause  processes one clause c w.r.t. to l.
   If l occurs in c it returns Nothing (clause omitted)
   if ¬l  occurs in c it removesfrom c ¬l  and returns the result as Some
   otherwise it returns Some c
*)

Definition processOneClause (c : Clause)(l : Literal) : option Clause :=
  processOneClause_aux1 c l (lit_in_clause l c) .

Definition processOneClause_proof (c : Clause)(l : Literal)
(cp : TreeProof) (lp : TreeProof) : option TreeProof :=
  processOneClause_aux1_proof c l (lit_in_clause l c)  cp lp.

Lemma processOneClause_correct : forall (as0 : Assumption)
                                        (c : Clause)(l : Literal)
                                         (cp : TreeProof) (lp : TreeProof),

    CorrectProof as0 c cp /\ CorrectProof as0 [ l ]  lp
    -> CorrectOptionProof as0 (processOneClause c l) (processOneClause_proof c l cp lp).
Proof .
  intros .
  apply processOneClause_aux1_correct .
  assumption .
Qed.

(*--------------------------------------------------------------------------*)

Definition processClausesaux (c : option Clause)(ih : list Clause) : list Clause :=
  match c with
  | Some c => c :: ih
  | None =>  ih
  end.

Definition processTreeProofsaux (c : option Clause)
(t : option TreeProof)(iht : list TreeProof) : list TreeProof :=
  match c with
  | Some c => match t with
              | Some t => t :: iht
              | None =>  [] (*Should not happen*)
              end
  | None =>  iht
  end.

Lemma processClausesAuxCorrect : forall (al : Assumption) (c : option Clause)
(cs : list Clause) (tc : option TreeProof) (tcs : list TreeProof),
       (CorrectOptionProof al c tc) -> (CorrectProofList al cs tcs)
        -> CorrectProofList al (processClausesaux c cs)
                               (processTreeProofsaux c tc tcs).
Proof.
  intros al c ih.
  induction c.
  - intros.
    induction tc.
    + simpl.
      split.
      assumption.
      assumption.
    + contradiction.
  - intros.
    simpl in H0.
    unfold processClausesaux.
    induction tc.
    unfold processTreeProofsaux.
    assumption.
    simpl in *.
    assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* processClauses applies unit propagation w.r.t. l to all clauses,
   i.e. clauses containing l are omitted
        clauses containing ¬l have ¬l removed
	otherwise clauses are kept *)
Fixpoint processClauses (c : list Clause)(l : Literal): list Clause:=
  match c with
  | [] => []
  | hd :: tl => processClausesaux (processOneClause hd l) (processClauses tl l)
  end.

Fixpoint processTreeProofs (c : list Clause) (l : Literal)
(cp : list TreeProof) (lp : TreeProof) : list TreeProof :=
  match c with
  | [] => []
  | c :: cl =>
    match cp with
    | [] => [] (* Should not occur if correct *)
    | tc :: tcl => processTreeProofsaux (processOneClause c l)
                                        (processOneClause_proof c l tc lp)
                                        (processTreeProofs cl l tcl lp)
    end
  end.

Lemma processClauses_correct : forall (al : Assumption) (clauses : list Clause)
(l : Literal) (proofs : list TreeProof) (tp : TreeProof),
    CorrectProofList al clauses proofs ->
    CorrectProof al [l] tp ->
    CorrectProofList al (processClauses clauses l) (processTreeProofs clauses l proofs tp).
Proof.
  intros al clauses l.
  induction clauses as [| c tl IH].
  * intros.
    destruct proofs.
    + simpl. auto.
    + simpl. auto.
  * intros.
    destruct proofs.
    + simpl in *. contradiction.
    + simpl in *.
      induction tp.
      - destruct (processOneClause_aux1 c l (lit_in_clause l c)) eqn:Hc.
        apply processClausesAuxCorrect.
      -- apply processOneClause_correct.
         destruct H.
         split.
         assumption.
         assumption.
      -- apply IH.
         destruct H.
         assumption.
         assumption.
      -- apply processClausesAuxCorrect.
          --- apply processOneClause_correct.
              destruct H.
              split.
              assumption.
              assumption.
          --- apply IH.
              destruct H.
              assumption.
              assumption.
      - apply processClausesAuxCorrect.
        -- apply processOneClause_correct.
           destruct H.
           split.
           assumption.
           assumption.
        -- apply IH.
           destruct H.
           assumption.
           assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* addClauseToSplitClauses adds  clause to SplitClauses

   by putting it into the right category depending on
       whether clause is [] unit clause or long clause
 *)
(* was splitStep *)


Definition addClauseToSplitClauses (clause : Clause) (IH : SplitClauses) : SplitClauses :=
  match IH with
  | (clausesIH, literalsIH, boolIH) =>
    match clause with
      | [] => ([], [], true)
      | [l] =>
          (clausesIH, l :: literalsIH, boolIH)
      | _ =>
          (clause :: clausesIH, literalsIH, boolIH)
    end
  end.

Definition addClauseToSplitClausesProofs (clause : Clause) (tp : TreeProof) (IH : SplitTreeProofs) : SplitTreeProofs:=
  match IH with
  | (clausestpIH, literalstpIH, emptyIH) =>
    match clause with
      | [] => ([], [], Some tp)
      | [l] =>
          (clausestpIH, tp :: literalstpIH, emptyIH)
      | _ =>
          (tp :: clausestpIH, literalstpIH, emptyIH)
    end
  end.

Lemma CorrectSplitStep :
  forall (al : Assumption) (c : Clause) (IHc : SplitClauses)
         (t : TreeProof) (IHt : SplitTreeProofs),
  CorrectProof al c t ->
  CorrectSplit al IHc IHt ->
  CorrectSplit al (addClauseToSplitClauses c IHc) (addClauseToSplitClausesProofs c t IHt).
Proof.
  intros al c IHc t IHt Hcp Hcs.
  unfold addClauseToSplitClauses, addClauseToSplitClausesProofs.
  destruct IHc as [[clausesIH literalsIH] boolIH].
  destruct IHt as [[clausestpIH literalstpIH] emptyIH].
  destruct c as [| l c_tail].
  - (* Case: c is an empty clause *)
    simpl. auto.
  - destruct c_tail as [| l_tail].
    + (* Case: c is a singleton clause *)
      simpl.
      split; [| split]; simpl; auto.
      *
        apply Hcs.
      * (* Goal 2: CorrectProof al [l] t /\ CorrectLiteralProof al literalsIH literalstpIH *)
        split.
        -- apply Hcp.
        -- apply Hcs.
      * (* Goal 3: CorrectOptionTreeProof' al boolIH emptyIH *)
        apply Hcs.
    + (* Case: c has more than one literal *)
      simpl.
      split; [| split]; simpl; auto.
      (* Prove the remaining goals *)
      * (* Goal 1: CorrectProof al [l] t /\ CorrectLiteralProof al literalsIH literalstpIH *)
        split.
        -- apply Hcp.
        -- apply Hcs.
      * (* Goal 2: CorrectOptionTreeProof' al boolIH emptyIH *)
        apply Hcs.
      * (* Goal 3: CorrectOptionTreeProof' al boolIH emptyIH *)
        apply Hcs.
Qed.

(*--------------------------------------------------------------------------*)

(* split clause into SplitClauses
   i.e. into list of long clauses, unit clauses and a possible empty clause *)

Fixpoint splitClauses (clauses : list Clause) : SplitClauses :=
  match clauses with
  | [] => ([], [], false)
  | c :: cs =>
      addClauseToSplitClauses c (splitClauses cs)
  end.

Fixpoint splitProofs (clauses : list Clause) (proofs : list TreeProof) : SplitTreeProofs :=
  match clauses with
  | [] => ([], [], None)
  | c :: cs =>
        match proofs with
        | [] => ([], [], None)
        | t :: ts =>
          addClauseToSplitClausesProofs c t (splitProofs cs ts)
        end
  end.

Lemma CorrectSplitProofs :
  forall (al : Assumption) (c : list Clause) (t : list TreeProof),
  CorrectProofList al c t ->
  CorrectSplit al (splitClauses c) (splitProofs c t).
Proof.
  intros al c.
  induction c.
  - intros t cpl.
    simpl in *. auto.
  - intros t cpl.
    destruct t.
    + simpl in *. contradiction.
    + simpl in *.
      destruct cpl.
      specialize (IHc t0).
      apply CorrectSplitStep.
      * assumption.
      * apply IHc.
        -- assumption.
Qed.

(* Function processes a list of clauses w.r.t. one literal
   and splits it up into an element of SplitClauses *)
Definition processAndSplitClausesWithLit (clauses : list Clause) (l : Literal)
           : SplitClauses :=
  let processed_clauses := processClauses clauses l in
  splitClauses processed_clauses.

(* Function to process TreeProofs and extract unit clauses *)
Definition process_and_extract_treeproofs
(clauses : list Clause) (l : Literal) (tpl: list TreeProof) (ltp : TreeProof)
: SplitTreeProofs :=
  let processed_proofs := processTreeProofs clauses l tpl ltp in
  splitProofs (processClauses clauses l) processed_proofs.

Lemma process_and_extract_correct :
  forall (al : Assumption) (clauses : list Clause) (proofs : list TreeProof)
         (l : Literal) (tp : TreeProof),
    CorrectProofList al clauses proofs ->
    CorrectProof al [l] tp ->
    CorrectSplit al (splitClauses (processClauses clauses l))
                     (splitProofs
                        (processClauses clauses l)
                        (processTreeProofs clauses l proofs tp)).
Proof.
  intros al clauses proofs l tp Hcpl Hcp.

  (* Appy CorrectSplitProofs *)
  apply CorrectSplitProofs.
  - apply processClauses_correct.
    + exact Hcpl.
    + assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* Process a list of Literals denoting a list of Unit Clauses with one literal l

   Done by removing literals equal to l
   and in case of a literal equal to ¬l returning ([],true) since
            we obtained the empty clause by unit resolution
   and otherwise keeps the literals
*)

Fixpoint processListLitsWithLit (literals : list Literal) (l : Literal) : SplitLiterals :=
  match literals with
  | [] => ([], false)
  | hd :: tl =>
      match literal_eqb hd l with
      | true => processListLitsWithLit tl l
      | false =>
          match literal_eqb hd (negate l) with
          | true => ([], true)
          | false =>
              let (remaining_literals, found_negation) := processListLitsWithLit tl l in
              (hd :: remaining_literals, found_negation)
          end
      end
  end.

Fixpoint remove_treeproof (literals : list Literal) (proofs : list TreeProof)
(l : Literal) (tp : TreeProof) : SplitLiteralsProof :=
  match literals with
  | [] => ([], None)
  | lhd :: lls =>
    match proofs with
    | [] => ([], None)
    | thd :: tls =>
      match literal_eqb lhd l with
      | true => remove_treeproof lls tls l tp
      | false =>
          match literal_eqb lhd (negate l) with
          | true => ([], Some (ures thd tp))
          | false =>
              let result := remove_treeproof lls tls l tp in
              let remaining_proofs := (fst result) in
              let found_negation := snd result in
              (thd :: remaining_proofs, found_negation)
          end
      end
    end
  end.

Lemma z3_formula_eq_eq : forall f1 f2,
  z3_formula_eq f1 f2 = true <-> f1 = f2

with list_z3_formula_eq_eq : forall l1 l2,
  list_z3_formula_eq l1 l2 = true <-> l1 = l2.
Proof.
  - (* z3_formula_eq_eq *)
    induction f1; intros f2; split.
    + destruct f2; simpl; try discriminate.
      intros.
      apply String.eqb_eq in H. subst. reflexivity.
    + intros H. subst. simpl. apply String.eqb_eq. reflexivity.
    + destruct f2; simpl; try discriminate.
      intros.
      apply list_z3_formula_eq_eq in H. subst. reflexivity.
    + intros H. subst. simpl. apply list_z3_formula_eq_eq. reflexivity.
    + destruct f2; simpl; try discriminate.
      intros.
      apply list_z3_formula_eq_eq in H. subst. reflexivity.
    + intros H. subst. simpl. apply list_z3_formula_eq_eq. reflexivity.
    + destruct f2; simpl; try discriminate.
      intros.
      apply andb_true_iff in H as [H1 H2].
      apply IHf1_1 in H1. apply IHf1_2 in H2. subst. reflexivity.
    + intros H. subst. simpl. apply andb_true_iff. split.
      * apply IHf1_1. reflexivity.
      * apply IHf1_2. reflexivity.
    + destruct f2; simpl; try discriminate.
      intros.
      apply IHf1 in H. subst. reflexivity.
    + intros H. subst. simpl. apply IHf1. reflexivity.

  - (* list_z3_formula_eq_eq *)
    induction l1; intros l2; split.
    + destruct l2; simpl; try discriminate. reflexivity.
    + intros H. subst. reflexivity.
    + destruct l2; simpl; try discriminate.
      intros.
      apply andb_true_iff in H as [H1 H2].
      apply z3_formula_eq_eq in H1.
      apply IHl1 in H2. subst. reflexivity.
    + intros H. subst. simpl. apply andb_true_iff. split.
      * apply z3_formula_eq_eq. reflexivity.
      * apply IHl1. reflexivity.
Qed.

Lemma pos_z3_formula_eq_eq : forall p1 p2,
  pos_z3_formula_eq p1 p2 = true <-> p1 = p2.
Proof.
  intros p1 p2.
  split.
  - (* -> direction *)
    destruct p1, p2; simpl; try discriminate.
    + (* pos_z3var *)
      intros H. apply String.eqb_eq in H. subst. reflexivity.
    + (* pos_and *)
      intros H. apply list_z3_formula_eq_eq in H. subst. reflexivity.
    + (* pos_or *)
      intros H. apply list_z3_formula_eq_eq in H. subst. reflexivity.
    + (* pos_imply *)
      intros.

      apply andb_true_iff in H as [H1 H2].
      apply z3_formula_eq_eq in H1.
      apply z3_formula_eq_eq in H2.
      subst. reflexivity.
  - (* <- direction *)
    intros H. subst.
    destruct p2; simpl.
    + apply String.eqb_eq. reflexivity.
    + apply list_z3_formula_eq_eq. reflexivity.
    + apply list_z3_formula_eq_eq. reflexivity.
    + apply andb_true_iff. split; apply z3_formula_eq_eq; reflexivity.
Qed.

(* Specification Lemma *)

Lemma literal_eqb_eq : forall l1 l2,
  literal_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2.
  split.
  - destruct l1, l2; simpl; try discriminate.
    + (* pos case *)
      intros H.
      apply pos_z3_formula_eq_eq in H.
      subst. reflexivity.
    + (* neg case *)
      intros H.
      apply pos_z3_formula_eq_eq in H.
      subst. reflexivity.
  - intros H. subst.
    destruct l2; simpl.
    + apply pos_z3_formula_eq_eq. reflexivity.
    + apply pos_z3_formula_eq_eq. reflexivity.
Qed.

Lemma literal_eqb_refl : forall l1 l2 : Literal,
  l1 = l2 -> literal_eqb l1 l2 = true.
Proof.
  intros l1 l2 H. subst.
  destruct l2; simpl.
  - apply pos_z3_formula_eq_eq. reflexivity.
  - apply pos_z3_formula_eq_eq. reflexivity.
Qed.

Lemma correct_resolution :
  forall al l t1 t2,
    CorrectProof al [negate l] t1 ->
    CorrectProof al [l] t2 ->
    CorrectProof al [] (ures t1 t2).
Proof.
  intros al l t1 t2 H1 H2.
  unfold CorrectProof in *.
  simpl in *.
  rewrite H1, H2.
  simpl.
  rewrite literal_eqb_refl.
  reflexivity.
  reflexivity.
Qed.

Lemma correct_processListLitsWithLit :
  forall al ls ts l t,
    CorrectLiteralProof al ls ts ->
    CorrectLiteralProof al [l] [t] ->
    CorrectSplitLiterals al (processListLitsWithLit ls l) (remove_treeproof ls ts l t).
Proof.
  intros al ls.
  induction ls as [| l' ls' IH]; intros ts l t Hls Hlt.
  - (* Base case: ls = [] *)
    simpl in *.
    auto.
  - (* Inductive case: ls = l' :: ls' *)
    destruct ts as [| t' ts'].
    + (* ts = [] but ls ≠ [] *)
      simpl in Hls. contradiction.
    + (* ts = t' :: ts' *)
      simpl in *.
      destruct Hls as [Hhead Htail].
      remember (literal_eqb l' l) as eq_ll.
      destruct eq_ll.
      * (* Case: l' = l, skip this literal *)
        apply IH; assumption.
      * (* Case: l' ≠ l *)
        remember (literal_eqb l' (negate l)) as eq_opp.
        destruct eq_opp.
        -- (* Case: l' = negate l *)
           symmetry in Heqeq_opp.
           apply literal_eqb_eq in Heqeq_opp.
           subst l'.
           simpl.
           split.
           ++ constructor.
           ++ (* CorrectOptionTreeProof' al true (Some (ures t' t)) *)
              apply correct_resolution with l; [assumption | exact (proj1 Hlt)].
        -- (* Case: l' is unrelated *)
           simpl.
           specialize (IH ts' l t Htail Hlt).
           destruct (processListLitsWithLit ls' l) as [lits b].
           destruct (remove_treeproof ls' ts' l t) as [lt bt].
           simpl in IH.
           destruct IH as [IH_lits IH_opt].
           split.
           ++ constructor; assumption.
           ++ assumption.
Qed.

(*--------------------------------------------------------------------------*)

Definition choose_proof (a b : option TreeProof) : option TreeProof :=
  match a with
  | Some _ => a
  | None => b
  end.

Lemma chooseOptionProofCorrect :
  forall (al : Assumption) (b1 b2 : bool) (t1 t2 : option TreeProof),
    CorrectOptionTreeProof' al b1 t1 ->
    CorrectOptionTreeProof' al b2 t2 ->
    CorrectOptionTreeProof' al (b1 || b2) (choose_proof t1 t2).
Proof.
  intros al b1 b2 t1 t2 H1 H2.
  destruct b1, b2; simpl in *.
  - (* Case: b1 = true, b2 = true *)
    destruct t1 as [tp1|], t2 as [tp2|]; simpl in *; try contradiction; auto.
  - (* Case: b1 = true, b2 = false *)
    destruct t1 as [tp1|]; simpl in *; try contradiction; auto.
  - (* Case: b1 = false, b2 = true *)
    destruct t2 as [tp2|]; simpl in *; try contradiction; auto.
    destruct t1 as [tp1|]. contradiction.
    auto.
  - (* Case: b1 = false, b2 = false *)
    destruct t1. contradiction.
    auto.
Qed.

(*--------------------------------------------------------------------------*)

(* combineSplitClausesSplitLits combines SplitClauses and SplitLiterals
   into one SplitClauses *)

Definition combineSplitClausesSplitLits (sc : SplitClauses) (rl : SplitLiterals) :
SplitClauses :=
match sc with
| (processed_clauses, unit_literals, contains_empty) =>
  match rl with
  | (filtered_literals, found_negation) =>
    (processed_clauses, unit_literals ++ filtered_literals,
            contains_empty || found_negation)
  end
end.

Definition combineSplitTreeProofs (st : SplitTreeProofs) (rt : SplitLiteralsProof) :
SplitTreeProofs :=
match st with
| (processed_clauses, unit_literals, contains_empty) =>
  match rt with
  | (filtered_literals, found_negation) =>
    (processed_clauses, unit_literals ++ filtered_literals,
            (choose_proof contains_empty found_negation))
  end
end.

Lemma CorrectLiteralProof_app :
  forall al l1 l2 t1 t2,
    CorrectLiteralProof al l1 t1 ->
    CorrectLiteralProof al l2 t2 ->
    CorrectLiteralProof al (l1 ++ l2) (t1 ++ t2).
Proof.
  intros al l1.
  induction l1 as [| l l1' IH]; intros l2 t1 t2 H1 H2.
  - (* Base case: l1 = [] *)
    simpl in *. destruct t1; simpl in *; try assumption; contradiction.
  - (* Inductive case: l1 = l :: l1' *)
    destruct t1 as [| tp t1']; simpl in *; try contradiction.
    destruct H1 as [Hhead Htail].
    split.
    + exact Hhead.
    + apply IH; assumption.
Qed.

Lemma CorrectCombineSplit :
  forall (al : Assumption) (Sc : SplitClauses) (St : SplitTreeProofs)
         (Rl : SplitLiterals) (Rt : SplitLiteralsProof),
  CorrectSplit al Sc St ->
  CorrectSplitLiterals al Rl Rt ->
  CorrectSplit al (combineSplitClausesSplitLits Sc Rl) (combineSplitTreeProofs St Rt).
Proof.
  intros.
  destruct Sc.
  destruct St.
  destruct p.
  destruct p0.
  destruct Rl.
  destruct Rt.

  unfold CorrectSplit.

  destruct H.
  destruct H1.
  destruct H0.

  repeat split.
  assumption.
  apply CorrectLiteralProof_app. assumption. assumption.
  apply chooseOptionProofCorrect. assumption. assumption.
Qed.

(*--------------------------------------------------------------------------*)


Lemma correct_singleton_literal :
  forall (al : Assumption) (l : Literal) (tp : TreeProof),
    CorrectProof al [l] tp <-> CorrectLiteralProof al [l] [tp].
Proof.
  intros al l tp.
  split.
  - (* -> direction *)
    intros H.
    simpl.
    split; [assumption | constructor].
  - (* <- direction *)
    intros [H _].
    exact H.
Qed.


(* process clauses and literals with one lit, combine them and split the result
     into SplitClauses *)
Definition propagationStep'
  (clauses : list Clause)
  (literals : list Literal)
  (l : Literal) : SplitClauses :=
  combineSplitClausesSplitLits (processAndSplitClausesWithLit clauses l)
    (processListLitsWithLit literals l).

(* Variant of propagationStep'
   where we bundle the arguments of propagationStep'
   as an element of PreparePropStep *)
Definition propagationStep (p : PreparePropStep) : SplitClauses :=
  match p with
    (c,ls,l) => propagationStep' c ls l
  end.


Definition propagationStepProofs' (clauses : list Clause)
  (literals : list Literal) (l : Literal) (proofs_c proofs_l : list TreeProof)
  (tp : TreeProof) : SplitTreeProofs :=
  combineSplitTreeProofs (process_and_extract_treeproofs clauses l proofs_c tp)
    (remove_treeproof literals proofs_l l tp).

Definition propagationStepProofs (p : PreparePropStep)
  (pt : PreparePropStepProofs) : SplitTreeProofs :=
  match p with
    (c,ls,l) =>
      match pt with
        (cp,lsp,lp) =>
          propagationStepProofs' c ls l cp lsp lp
      end
  end.

(* propagationStepCorrect *)
Lemma propagationStepCorrect' :
  forall (al : Assumption)
         (clauses : list Clause)
         (literals : list Literal)
         (l : Literal)
         (proofs_c proofs_l : list TreeProof)
         (tp : TreeProof),
    CorrectProofList al clauses proofs_c ->
    CorrectLiteralProof al literals proofs_l ->
    CorrectProof al [l] tp ->
    CorrectSplit al
      (propagationStep' clauses literals l)
      (propagationStepProofs' clauses literals l proofs_c proofs_l tp).
Proof.
  intros.

  apply CorrectCombineSplit.
  + unfold processAndSplitClausesWithLit.
    unfold process_and_extract_treeproofs.
    apply process_and_extract_correct.
    assumption.
    assumption.
  + apply correct_processListLitsWithLit.
    assumption.
    apply correct_singleton_literal. assumption.
Qed.


Lemma propagationStepCorrect :
  forall (al : Assumption)
         (p : PreparePropStep)
         (pt : PreparePropStepProofs),
    CorrectPreparePropStep al p pt ->
    CorrectSplit al
      (propagationStep p)
      (propagationStepProofs p pt).
Proof.
  intros.
  destruct p, pt.
  destruct p, p0.
  unfold propagationStep,propagationStepProofs.
  unfold CorrectPreparePropStep in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  apply propagationStepCorrect'.
  assumption.
  assumption.
  assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* makes one unit propagation step on clauses and literals:
   if there is a literal it processes the clauses and literals returning
     an elemet for SplitClauses
   otherwise it returns (c,[],false), i.e. does nothing *)
Definition clausesLiteralsUnitPropagationStep (c : list Clause) (ls : list Literal) :
SplitClauses :=
  match ls with
    | [] => (c, ls, false)
    | l :: ls =>
      propagationStep' c ls l
  end.

Definition clausesLiteralsUnitPropagationStepSC (sc : SplitClauses) : SplitClauses :=
  match sc with
  | (c,l,b) =>
      match b with
      | true => ([], [],true)
      | false=> clausesLiteralsUnitPropagationStep c l
      end
        end.

Definition clausesLiteralsUnitPropagationStepProof (c : list Clause) (ls : list Literal)
(ctp : list TreeProof) (ltp : list TreeProof) :
SplitTreeProofs :=
  match ls with
    | [] => (ctp, ltp, None)
    | l :: ls =>
      match ltp with
      | [] => (ctp, ltp, None)
      | lt :: lts => propagationStepProofs' c ls l ctp lts lt
      end
  end.

Definition clausesLiteralsUnitPropagationStepProofSC (sc : SplitClauses)
   (tc : SplitTreeProofs) : SplitTreeProofs :=
  match sc with
  | (c,l,b) =>
      match tc with
      | (tc,tl,tb) =>
          match tb with
          | None => clausesLiteralsUnitPropagationStepProof c l tc tl
          | Some t => ([] , [], Some t)
          end
      end
  end.


Lemma clausesLiteralsUnitPropagationStep_correct :
  forall (al : Assumption)
         (c : list Clause)
         (ls : list Literal)
         (b : bool)
         (ctp ltp : list TreeProof)
         (bt : option TreeProof),
    CorrectSplit al (c, ls, b) (ctp, ltp, bt) ->
    CorrectSplit al
      (clausesLiteralsUnitPropagationStep c ls)
      (clausesLiteralsUnitPropagationStepProof c ls ctp ltp).
Proof.
  intros al c ls b ctp ltp bt Hsplit.
  destruct ls as [| l ls'].
  - (* Case: ls = [] *)
    simpl.
    destruct Hsplit.
    destruct H0.
    split.
    assumption.
    destruct ltp.
    auto.
    split.
    simpl in H0. assumption.
    contradiction.

  - (* Case: ls = l :: ls' *)
    destruct ltp as [| lt lts].
    + (* Subcase: ltp = [] *)
      simpl in *.
      destruct Hsplit as [Hc [Hl Hb]].
      (* Hl : CorrectLiteralProof al (l :: ls') [] *)
      (* But this is false by definition of CorrectLiteralProof *)
      inversion Hl.

    + (* Subcase: ltp = lt :: lts *)
      simpl.
      apply propagationStepCorrect'.

      unfold CorrectSplit in Hsplit.
      destruct Hsplit as [Hc [Hl Hb]].
      assumption.

      unfold CorrectSplit in Hsplit.
      destruct Hsplit as [Hc [Hl Hb]].
      simpl in Hl.
      destruct Hl.
      assumption.

      unfold CorrectSplit in Hsplit.
      destruct Hsplit as [Hc [Hl Hb]].
      simpl in Hl.
      destruct Hl.
      assumption.
Qed.


Lemma clausesLiteralsUnitPropagationStepSC_correct :
  forall (al : Assumption)
         (sc : SplitClauses)
         (tc : SplitTreeProofs),
    CorrectSplit al sc tc ->
    CorrectSplit al
      (clausesLiteralsUnitPropagationStepSC sc)
      (clausesLiteralsUnitPropagationStepProofSC sc tc) .
Proof.
  intros.
  destruct sc.
  destruct p.
  destruct tc.
  destruct p.
  destruct b.
  destruct o.
  unfold clausesLiteralsUnitPropagationStepSC.
  unfold clausesLiteralsUnitPropagationStepProofSC.
  unfold CorrectSplit.
  split.
  unfold CorrectProofList.
  auto.
  split.
  unfold CorrectLiteralProof.
  auto.
  unfold CorrectOptionTreeProof'.
  unfold CorrectProof.
  unfold CorrectSplit in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold CorrectOptionTreeProof' in H4.
  unfold CorrectProof in H4.
  assumption.
  unfold clausesLiteralsUnitPropagationStepSC.
  unfold clausesLiteralsUnitPropagationStepProofSC.
  unfold CorrectSplit in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold CorrectOptionTreeProof' in H4.
  contradiction.
  destruct o.
  unfold clausesLiteralsUnitPropagationStepSC.
  unfold clausesLiteralsUnitPropagationStepProofSC.
  unfold CorrectSplit in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold CorrectOptionTreeProof' in H4.
  contradiction.
  apply (clausesLiteralsUnitPropagationStep_correct al l l0 false l1 l2 None).
  assumption.
Qed.

(* ----------  iteratePropagator Clause Level ----------- *)

(* checks if sc is already terminated or not
   if it is terminated returns sc,
   otherwise we have divided up the sc into  a list of clauses, literals, and a literal
     from which we obtain an element of PreparePropStep.
     now we apply ih to it
         for ih we will use   (iteratePropagatorLoop n)
*)

Definition selectAndRunPropagator
  (sc : SplitClauses)
  (cont : SplitClauses -> SplitClauses) : SplitClauses :=
  match sc with
  | (c, ls, b) =>
      match b with
      | true => sc
      | _ => match ls with
             | [] => sc
             | l :: ls => cont (propagationStep (c , ls , l))
             end
      end
  end.


(* runs n times propagationStep on its argument
   while after each iteration executing selectAndRunPropagator
   in order to check whether we are finished and if not splitting
   the result into a an element of PreparePropStep
*)
Fixpoint iteratePropagator (n : nat) (p : SplitClauses) : SplitClauses :=
  match n with
  | S n => selectAndRunPropagator p (iteratePropagator n)
  | 0 =>  p
  end.

(* runs n times propagationStep' on its arguments,
   where in each iteration checking first whether we have finished
   and if not splitting it into an element of PreparePropStep
*)



(* ----------  iteratePropagator ProofTree Level ----------- *)

Definition selectAndRunPropagatorProof
  (sc : SplitClauses)
  (sp : SplitTreeProofs)
  (contp : SplitClauses -> SplitTreeProofs -> SplitTreeProofs) : SplitTreeProofs :=
  match sc with
  | (c, ls, b) =>
      match b with
      | true => sp
      | _ => match ls with
             | [] => sp
             | l :: ls =>
                 match sp with
                 | (cp , lsp ,op) =>
                     match lsp with
                     | [] => defaulSplitTreeProofs  (* doesn't occur if correct *)
                     | lp :: lsp =>
                         match op with
                         | None =>  contp
                                      (propagationStep  (c , ls , l))
                                      (propagationStepProofs (c , ls , l) (cp , lsp, lp))
                         | Some _ => defaulSplitTreeProofs (* doesn't occur if correct *)

                         end
                     end
                 end
             end
      end
  end.

Fixpoint iteratePropagatorProof (n : nat) (sc : SplitClauses)
         (sp : SplitTreeProofs)  : SplitTreeProofs :=
  match n with
  | S n => selectAndRunPropagatorProof sc sp
            (iteratePropagatorProof n)
  | 0 =>  sp
  end.

(* ----------  iteratePropagator Correctness Level ----------- *)

Lemma selectAndRunPropagatorCorrect :
  forall (al : Assumption)
         (sc : SplitClauses)  (sp : SplitTreeProofs)
         (cont : SplitClauses -> SplitClauses)
         (contp : SplitClauses -> SplitTreeProofs -> SplitTreeProofs),
    CorrectSplit al sc sp
    -> (forall (sc' : SplitClauses)(sp' : SplitTreeProofs),
           CorrectSplit al sc' sp'
           -> CorrectSplit al (cont sc') (contp sc' sp'))
    -> CorrectSplit al
         (selectAndRunPropagator sc cont)
         (selectAndRunPropagatorProof sc sp contp).
Proof.
  intros.
  destruct sc.
  destruct p.
  destruct b.
  unfold selectAndRunPropagator, selectAndRunPropagatorProof.
  assumption.
  destruct l0.
  unfold selectAndRunPropagator, selectAndRunPropagatorProof.
  assumption.
  destruct sp.
  destruct p.
  destruct l3.
  unfold selectAndRunPropagator, selectAndRunPropagatorProof.
  unfold CorrectSplit in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold CorrectLiteralProof in H3.
  contradiction.
  destruct o.
  unfold selectAndRunPropagator, selectAndRunPropagatorProof.
  unfold CorrectSplit in H.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold CorrectOptionTreeProof' in H4.
  contradiction.
  unfold selectAndRunPropagator.
  unfold selectAndRunPropagatorProof.

  apply H0.
  unfold CorrectPreparePropStep.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  apply propagationStepCorrect.
  apply CorrectLiteralProofUnfold1 in H3.

  unfold CorrectPreparePropStep.
  repeat split.
  assumption.
  destruct H3.
  assumption.
  destruct H3.
  assumption.
Qed.

Lemma iteratePropagatorRewrite1 :
  forall (n : nat) (sc : SplitClauses),
    iteratePropagator  (S n) sc = selectAndRunPropagator sc (iteratePropagator n).
Proof.
  intros.
  reflexivity.
Qed.

Lemma iteratePropagatorProofRewrite1 :
  forall (n : nat) (sc : SplitClauses) (sp : SplitTreeProofs) ,
    iteratePropagatorProof (S n) sc sp = selectAndRunPropagatorProof sc sp (iteratePropagatorProof n).
Proof.
  intros.
  reflexivity.
Qed.

Lemma iteratePropagatorCorrect :
  forall (al : Assumption)(n : nat) (p : SplitClauses)(pt : SplitTreeProofs),
    CorrectSplit al p pt
    -> CorrectSplit al (iteratePropagator n p)  (iteratePropagatorProof n p pt).
Proof.
  intros al n.
  induction n.
  intros.
  unfold iteratePropagator, iteratePropagatorProof.
  + assumption.
  + intros. 
    rewrite iteratePropagatorProofRewrite1.
    rewrite iteratePropagatorRewrite1.
    apply selectAndRunPropagatorCorrect.
    - assumption.
    - apply IHn.
Qed.

(* ----------  iteratePropagator End ----------- *)

Definition splitClauses_to_bool (sc : SplitClauses) : bool :=
match sc with
| (c, l, b) => b
end.

Definition splitClauses_to_bool_proof (tp : SplitTreeProofs) : option TreeProof :=
match tp with
| (c, l, bt) => bt
end.

Lemma splitClauses_to_bool_correct :
forall (al : Assumption) (sc : SplitClauses) (tp : SplitTreeProofs),
CorrectSplit al sc tp ->
CorrectOptionTreeProof al (splitClauses_to_bool sc)
                      (splitClauses_to_bool_proof tp).
Proof.
intros.
destruct sc, tp.
destruct p, p0.
unfold splitClauses_to_bool, splitClauses_to_bool_proof.
destruct H as [H0 [H1 H2]].
destruct o.
destruct b.
unfold CorrectOptionTreeProof.
unfold BooltoOC.
unfold CorrectOptionTreeProof' in H2.
unfold CorrectOptionProof.
assumption.
contradiction.
destruct b.
contradiction.
assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* Check if a literal's string is in the seen list *)
Definition literal_in_seen (l : Literal) (seen : list Pos_Z3_Formula) : bool :=
  match l with
  | pos x => existsb (pos_z3_formula_eq x) seen
  | neg x => existsb (pos_z3_formula_eq x) seen
  end.

(* compute list of variables in a clause by adding them to seen *)
(* was update_seen_literals_in_clause *)
Fixpoint addVarsInClauseToSeen (c: Clause) (seen: list Pos_Z3_Formula) : list Pos_Z3_Formula :=
  match c with
  | [] => seen
  | l :: ls =>
      let lit_str := match l with
                    | pos x => x
                    | neg x => x
                    end in
      if literal_in_seen l seen then addVarsInClauseToSeen ls seen
      else addVarsInClauseToSeen ls (lit_str :: seen)
  end.

(* adds variables in a formula to a list of seen Strings *)
Fixpoint addVarsInForToSeen (f: Formula) (seen: list Pos_Z3_Formula) : list Pos_Z3_Formula :=
  match f with
  | [] => seen
  | c :: cs =>
      let updated_seen := addVarsInClauseToSeen c seen in
      addVarsInForToSeen cs updated_seen
  end.

(* Return length of a list *)
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

(* Calculate number of variables in f *)
Definition countVarsInFor (f: Formula) : nat :=
  length (addVarsInForToSeen f []).

(*--------------------------------------------------------------------------*)

Definition ConclusionWithDefault (al : Assumption) (t : TreeProof) : Clause :=
  OptionClauseToClause (correctConclusion al t).

Definition OptionTProofToTProof (otp : option TreeProof) : TreeProof :=
  match otp with
  | None => ass 0
  | Some t => t
  end.

Definition tpCorrect (al : Assumption) (t: TreeProof) : bool :=
 OptionClauseToBool (correctConclusion al t).

Lemma tpCorrectEqualsTrueAux :
forall (c : option Clause),
  OptionClauseToBool c = true ->
  c = Some (OptionClauseToClause c).
Proof.
intros.
destruct c.
simpl. reflexivity.
discriminate.
Qed.

Lemma tpCorrectEqualsTrue :
forall (al : Assumption) (t : TreeProof),
  tpCorrect al t = true ->
  correctConclusion al t = Some (ConclusionWithDefault al t).
Proof.
intros.
unfold ConclusionWithDefault.
apply tpCorrectEqualsTrueAux.
unfold tpCorrect in H.
assumption.
Qed.

Lemma tpCorrectEqualsTrueReverse :
forall (al : Assumption) (c : Clause) (t : TreeProof),
  correctConclusion al t = Some c ->
  tpCorrect al t = true.
Proof.
intros.
unfold tpCorrect.
rewrite H.
unfold OptionClauseToBool.
reflexivity.
Qed.

Lemma CorrectProofTrue :
forall (al : Assumption) (c : Clause) (t : TreeProof),
  CorrectProof al c t ->
  tpCorrect al t = true.
Proof.
intros.
unfold tpCorrect.
unfold CorrectProof in H.
rewrite H.
unfold OptionClauseToBool.
reflexivity.
Qed.

Lemma TP_from_Res_1 :
forall (al : Assumption) (t1 t2 : TreeProof),
  tpCorrect al (ures t1 t2) = true ->
  tpCorrect al t1 = true.
Proof.
intros.
unfold tpCorrect in *.
simpl in *.
apply correctConclusionResTrue1 in H.
assumption.
Qed.

Lemma TP_from_Res_2 :
forall (al : Assumption) (t1 t2 : TreeProof),
  tpCorrect al (ures t1 t2) = true ->
  tpCorrect al t2 = true.
Proof.
intros.
unfold tpCorrect in *.
simpl in *.
apply correctConclusionResTrue2 in H.
assumption.
Qed.

Lemma OptionTProofToTProofcorrect :
forall (al : Assumption)(c : option Clause) (t : option TreeProof),
  OptionClauseToBool c = true ->
  CorrectOptionProof al c t ->
  CorrectProof al (OptionClauseToClause c)(OptionTProofToTProof t).
Proof.
intros.
destruct c.
destruct t.
simpl in *. auto.
simpl in *. auto.
contradiction.
simpl in *. discriminate.
Qed.

(*--------------------------------------------------------------------------*)

Definition unitPropagationAndCheck (a : Assumption) : bool :=
  splitClauses_to_bool (iteratePropagator (countVarsInFor a) (splitClauses a)).

Definition unitPropagationAndCheckProof (a : Assumption) (tps : list TreeProof) : option TreeProof :=
  splitClauses_to_bool_proof (iteratePropagatorProof (countVarsInFor a) (splitClauses a)
                                (splitProofs a tps)).

Lemma unitPropagationAndCheckCorrect :
  forall (a : Assumption) (tps : list TreeProof),
    CorrectProofList a a tps
    -> CorrectOptionTreeProof a (unitPropagationAndCheck a)
         (unitPropagationAndCheckProof a tps).
Proof.
  intros.
  unfold unitPropagationAndCheck, unitPropagationAndCheckProof.
  apply splitClauses_to_bool_correct.
  apply iteratePropagatorCorrect.
  apply CorrectSplitProofs.
  assumption.
Qed.

(*--------------------------------------------------------------------------*)


Fixpoint createAssTreeProofsAux (n : nat) (f: Formula): list TreeProof :=
  match f with
  | [] => []
  | (c :: cs) =>
    (ass n) :: createAssTreeProofsAux (S n) cs
  end.

(* computes for each assumption a TreeProof of that assumption using an
   ass rule *)
(* was createAssTreeProofs *)
Definition createAssTreeProofs (f: Formula) : list TreeProof :=
  createAssTreeProofsAux 0 f.

Definition unitPropagationAndCheckWithAssProof  (a : Assumption) : option TreeProof
  :=  unitPropagationAndCheckProof a (createAssTreeProofs a).


Require Import Coq.Lists.List.
Import ListNotations.

Lemma nth_error_app_exact :
  forall (l : list Clause) (x : Clause) (l' : list Clause),
    nth_error (l ++ x :: l') (length l) = Some x.
Proof.
  intros l x l'.
  induction l as [| a ls IH].
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

Lemma nth_error_app :
forall (f al : Formula) (a : Clause) (n : nat),
  length al = n ->
  nth_error (al ++ a :: f) n = Some a.
  Proof.
  intros f al a n H.
  rewrite <- H.
  apply nth_error_app_exact.
Qed.

Lemma lengthTPAux :
forall (f al : Formula) (a : Clause) (n : nat),
  length al = n ->
  CorrectProof (al ++ a :: f) a (ass n).
Proof.
intros.
unfold CorrectProof.
simpl.
unfold findAssumption.
rewrite <- nth_error_app with f al a n.
auto.
assumption.
Qed.

Lemma append_cons_eq :
forall (f al : Formula) (a : Clause),
  al ++ a :: f = (al ++ [a]) ++ f.
Proof.
  intros.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Require Import Coq.Arith.PeanoNat.

Lemma plus_one_eq_succ : forall n : nat, n + 1 = S n.
Proof.
  intros n.
  apply Nat.add_1_r.
Qed.

Lemma length_app_singleton :
  forall (X : Type) (al : list X) (a : X),
    Datatypes.length (al ++ [a]) = S (Datatypes.length al).
Proof.
  intros X al a.
  induction al as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma length_app_cons : forall (X : Type) (al : list X) (a : X) (n : nat),
  length al = n -> length (al ++ [a]) = S n.
Proof.
  intros X al a n H.
  rewrite length_app_singleton.
  rewrite H.
  reflexivity.
Qed.

Lemma createAssTreeProofsAux_Correct :
  forall (f al : Formula) (n : nat),
  length al = n ->
  CorrectProofList (al ++ f) f (createAssTreeProofsAux n f).
Proof.
intro f.
induction f.
+ simpl. auto.
+ intros. simpl.
  split.
  apply lengthTPAux.
  assumption.
  rewrite append_cons_eq.
  apply IHf.
  apply length_app_cons.
  assumption.
Qed.

Lemma createAssTreeProofsAux1_Correct :
  forall (f : Formula),
  CorrectProofList ([] ++ f) f (createAssTreeProofs f).
Proof.
  intros.
  apply createAssTreeProofsAux_Correct.
  auto.
Qed.

Lemma emptyList_F :
  forall (f: Formula),
  [] ++ f = f.
Proof.
auto.
Qed.

Lemma createAssTreeProofs_Correct :
  forall (a : Assumption),
  CorrectProofList a a (createAssTreeProofs a).
Proof.
  intros.
  apply createAssTreeProofsAux1_Correct.
Qed.


Lemma unitPropagationAndCheckWithAssCorrect :
  forall (a : Assumption),
    CorrectOptionTreeProof a (unitPropagationAndCheck a)
         (unitPropagationAndCheckWithAssProof a).
Proof.
  intros.
  unfold unitPropagationAndCheckWithAssProof.
  apply unitPropagationAndCheckCorrect.
  apply createAssTreeProofs_Correct.
Qed.

(*--------------------------------------------------------------------------*)

Lemma nth_error_nil :
  forall (A : Type) (n : nat),
    nth_error (@nil A) n = None.
Proof.
  intros A n.
  destruct n; reflexivity.
Qed.

Lemma IsTrue_and : forall a b : bool,
  IsTrue (a && b) -> IsTrue a /\ IsTrue b.
Proof.
  intros a b H.
  split.
  - destruct a.
    + simpl. apply I.
    + simpl in H. destruct b; simpl in H; contradiction.
  - destruct b.
    + simpl. apply I.
    + simpl in H. destruct a; simpl in H; contradiction.
Qed.

Lemma head_clause_models :
  forall (m : Model) (h : Clause) (t : list Clause),
    Models_formula m (h :: t) ->
    Models_clause m h.
Proof.
  intros m h t H.
  unfold Models_formula in H.
  simpl in H.
  apply IsTrue_and in H as [Hh _].
  exact Hh.
Qed.

Lemma models_formula_clause_at_index :
  forall (m : Model) (f : Formula) (n : nat) (c : Clause),
    nth_error f n = Some c ->
    Models_formula m f ->
    Models_clause m c.
Proof.
  intros m f.
  induction f as [| h t IH]; intros n c Hnth Hmodels.
  - (* Base case: f = [] *)
    simpl in Hnth.
    pose proof (nth_error_nil Literal n) as Hnil.
    assert (Hcontr : None = Some c).
    {
      rewrite <- Hnth. symmetry. apply nth_error_nil.
    }
    inversion Hcontr.
  - (* Inductive case: f = h :: t *)
    destruct n as [| n'].
    + (* Case: n = 0, so c = h *)
      simpl in Hnth. inversion Hnth. subst c.
      unfold Models_formula in Hmodels. simpl in Hmodels.
      apply IsTrue_and in Hmodels as [Hh _].
      exact Hh.
    + (* Case: n = S n' *)
      simpl in Hnth.
      unfold Models_formula in Hmodels. simpl in Hmodels.
      apply IsTrue_and in Hmodels as [_ Ht].
      apply IH with (n := n') in Hnth; auto.
Qed.

Lemma models_formula_tail :
  forall (m : Model) (h : Clause) (t : list Clause),
    Models_formula m (h :: t) ->
    Models_formula m t.
Proof.
  intros m h t H.
  unfold Models_formula in H.
  simpl in H.
  apply IsTrue_and in H as [_ Ht].
  exact Ht.
Qed.

Lemma nth_error_entails :
  forall (al : list Clause) (c : Clause) (n : nat),
    nth_error al n = Some c -> entails al c.
Proof.
  intros al c n H.
  unfold entails.
  intros m Hm.
  unfold Models_clause.
  unfold IsTrue.
  unfold models_clause.
  induction al as [| h t IH].
  - unfold Models_formula in Hm.
    unfold models_formula in Hm. simpl in Hm.
    simpl in H.
    pose proof (nth_error_nil Literal n) as Hnil.
    assert (Hcontr : None = Some c).
    {
      rewrite <- H. symmetry. apply nth_error_nil.
    }
    inversion Hcontr.
  - destruct n as [| n'].
    + simpl in H. inversion H.
      apply head_clause_models in Hm.
      rewrite H1 in Hm.
      exact Hm.
    + simpl in H. apply models_formula_clause_at_index with t n'.
      assumption.
      apply models_formula_tail with h.
      assumption.
Qed.

Lemma processListLitsWithLit_from_empty_clause : forall l : Literal,
  removeLitFromClause l [] = [].
Proof.
  intros l.
  unfold removeLitFromClause.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma models_processListLitsWithLit_from_empty_clause : forall m l,
  (Models_clause m (removeLitFromClause l []) <->
  Models_clause m []).
Proof.
  intros m l.
  split.
  - (* Proving the f  orward direction *)
    intros H.
    rewrite processListLitsWithLit_from_empty_clause in H.
    exact H.
  - (* Proving the backward direction *)
    intros H.
    rewrite processListLitsWithLit_from_empty_clause.
    exact H.
Qed.

Lemma listZ3_Formula_eq_dec : forall l1 l2 : listZ3_Formula,
  {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1 l2.
  destruct (list_z3_formula_eq l1 l2) eqn:H.
  - left. apply list_z3_formula_eq_eq in H. exact H.
  - right. intros Heq. subst. 

    assert (list_z3_formula_eq l2 l2 = true) as Htrue.
    {
      apply list_z3_formula_eq_eq. reflexivity.
    }
    rewrite Htrue in H. discriminate.
Qed.

Lemma z3_formula_eq_neq : forall f1 f2,
  z3_formula_eq f1 f2 = false <-> f1 <> f2.
Proof.
  intros f1 f2.
  split.
  - (* -> direction *)
    intros Hfalse Heq.
    assert (Heq' := Heq).
    subst.
    rewrite <- z3_formula_eq_eq in Heq'.
    rewrite Heq' in Hfalse.
    discriminate.
  - (* <- direction *)
    intros Hneq.
    destruct (z3_formula_eq f1 f2) eqn:H.
    + apply z3_formula_eq_eq in H. contradiction.
    + reflexivity.
Qed.

Lemma Z3_Formula_eq_dec : forall l1 l2 : Z3_Formula,
  {l1 = l2} + {l1 <> l2}.
Proof.
  intros l1 l2.
  destruct (z3_formula_eq l1 l2) eqn:H.
  - left. apply z3_formula_eq_eq in H. assumption.
  - right.
    apply z3_formula_eq_neq. assumption.
Qed.

Lemma pos_z3_formula_eq_dec :
  forall p1 p2 : Pos_Z3_Formula, {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
  - apply String.string_dec.
  - apply listZ3_Formula_eq_dec.
  - apply listZ3_Formula_eq_dec.
  - apply Z3_Formula_eq_dec.
  - apply Z3_Formula_eq_dec.
Qed.

Lemma lit_eq_dec : forall a b : Literal, {a = b} + {a <> b}.
Proof.
   intros a b.
   destruct a as [s1 | s1]; destruct b as [s2 | s2].
   - destruct (pos_z3_formula_eq_dec s1 s2) as [Heq | Hneq].
    + left. now f_equal.
    + right. intros H. inversion H. contradiction.
   - right. intro H. inversion H.
   - right. intro H. inversion H.
   - destruct (pos_z3_formula_eq_dec s1 s2) as [Heq | Hneq].
    + left. now f_equal.
    + right. intros H. inversion H. contradiction.
Qed.

Lemma pos_z3_formula_eq_false_neq :
  forall p p0 : Pos_Z3_Formula,
    pos_z3_formula_eq p p0 = false -> p <> p0.
Proof.
  intros p p0 Hfalse Heq.
  apply pos_z3_formula_eq_eq in Heq.
  rewrite Heq in Hfalse.
  discriminate.
Qed.

Lemma literal_eqb_spec :
  forall x y, reflect (x = y) (literal_eqb x y).
Proof.
  intros x y.
  destruct x, y; simpl.
  - destruct (pos_z3_formula_eq p p0) eqn:Heq.
    + apply pos_z3_formula_eq_eq in Heq. subst. apply ReflectT. reflexivity.
    + apply ReflectF. intros H. inversion H. subst.
      apply pos_z3_formula_eq_false_neq in Heq. contradiction.
  - apply ReflectF. intros H. inversion H.
  - apply ReflectF. intros H. inversion H.
  - destruct (pos_z3_formula_eq p p0) eqn:Heq.
    + apply pos_z3_formula_eq_eq in Heq. subst. apply ReflectT. reflexivity.
    + apply ReflectF. intros H. inversion H. subst.
      apply pos_z3_formula_eq_false_neq in Heq. contradiction.
Qed.

Lemma literal_eqb_neq :
forall l1 l2 : Literal,
  literal_eqb l1 l2 = false -> l1 <> l2.
Proof.
  intros l1 l2 Hfalse Heq.
  apply literal_eqb_eq in Heq.
  rewrite Heq in Hfalse.
  discriminate.
Qed.

Lemma remove_l_from_cons_l : forall
(ls : list Literal)
(l : Literal), ((removeLitFromClause l (l :: ls)) =
(removeLitFromClause l ls)).
Proof.
  intros.
  cbn.
  destruct literal_eqb eqn:Ha.
  + destruct (literal_eqb_spec l l) as [Heq | Hneq].
    - reflexivity. (* because the if-branch is the same as the RHS *)
    - contradiction. (* l = l, so this branch is impossible *)
  + apply literal_eqb_neq in Ha. contradiction.
Qed.

Lemma models_literal_negated_contradiction : forall (m : Model) (l : Literal),
  models_literal m (negate l) = true -> models_literal m l = true -> False.
Proof.
  intros m l Hlit1 Hlit2.
  unfold models_literal in *.
  destruct l.
  - (* Case: l = pos x *)
    simpl in *. rewrite Hlit2 in Hlit1. discriminate Hlit1.
  - (* Case: l = neg x *)
    simpl in *. rewrite Hlit1 in Hlit2. apply negb_true_iff in Hlit2. discriminate Hlit2.
Qed.

Lemma models_ls : forall
  (m : Model)
  (ls : list Literal)
  (l : Literal),
  Models_clause m ((negate l) :: ls) ->
  Models_clause m [l] ->
  Models_clause m ls.
Proof.
  intros m ls l H1 H2.
  unfold Models_clause in *.
  simpl in H1.
  unfold IsTrue in *.
  destruct (models_literal m (negate l)) eqn:Hlit1.
  - simpl in H2.
    destruct (models_literal m l) eqn:Hlit2.
    + simpl in H2. destruct H1. exfalso. apply models_literal_negated_contradiction with m l.
      * assumption.
      * assumption.
    + simpl in *. contradiction.
  - exact H1.
Qed.

Lemma models_c_implies_models_l_or_ls:
  forall (m : Model) (l' : Literal) (ls : list Literal),
  Models_clause m (l' :: ls) ->
  Models_clause m [l'] \/ Models_clause m ls.
Proof.
  intros m l' ls H.
  unfold Models_clause in *.
  simpl in H.
  unfold IsTrue in *.
  destruct (models_literal m l') eqn:Hlit.
  - left. simpl. rewrite Hlit. reflexivity.
  - right. exact H.
Qed.

Lemma removeLitFromClause_cons_neq :
  forall l l' ls,
    l <> l' ->
    removeLitFromClause l (l' :: ls) = l' :: removeLitFromClause l ls.
Proof.
  intros l l' ls Hneq.
  simpl.
  destruct (literal_eqb_spec l l') as [Heq | Hneq'].
  - contradiction.
  - reflexivity.
Qed.

Lemma removeLitFromClause_equiv :
  forall l c,
    removeLitFromClause l c = remove lit_eq_dec l c.
Proof.
  intros l c.
  induction c as [| hd tl IH].
  - reflexivity.
  - simpl. destruct (literal_eqb_spec l hd) as [Heq | Hneq].
    + subst. rewrite <- IH.
      destruct (lit_eq_dec hd hd) as [_ | n]; [reflexivity | contradiction].
    + simpl. rewrite IH.
      destruct (lit_eq_dec l hd) as [Heq' | Hneq'].
      * contradiction.
      * reflexivity.
Qed.

(* Lemma 5    l not= l’   implies    remove  l  (l’ :: c’) = l’  :: (remove l c’)*)
Lemma rewrite_removal :
  forall (l l' : Literal) (ls : list Literal),
  l'<>l ->
  (removeLitFromClause l (l'::ls)) =
  (l' :: (remove lit_eq_dec l ls)).
Proof.
  intros.
  unfold removeLitFromClause.
  simpl.
  (*Rewrite the assumption to make the proof simpler*)
  assert (l <> l') as H_neq_rev by auto.
  destruct (lit_eq_dec l l') as [H_eq | H_neq].
  - (* Case where l = l' *)
    contradiction.
  - (* Case where l <> l' *)
    destruct (literal_eqb_spec l l') as [Heq | Hneq'].
    + (* Case: l = l' *)
    subst.
    contradiction. (* because you have H : l' <> l *)
    + (* Case: l <> l' *)
    rewrite <- removeLitFromClause_cons_neq; [| assumption].
    rewrite removeLitFromClause_equiv.
    simpl.
    destruct lit_eq_dec.
    contradiction.
    reflexivity.
Qed.

Lemma m_models_ls_implies_m_models_l_colon_ls :
  forall (m : Model) (l' : Literal) (ls : list Literal),
  Models_clause m ls ->
  Models_clause m (l' :: ls).
Proof.
  intros m l' ls Hls.
  unfold Models_clause in *.
  simpl.
  destruct (models_literal m l') eqn:Hlit.
  - simpl. auto.
  - simpl. exact Hls.
Qed.

Lemma IsTrue_or_reverse : forall a b : bool,
  IsTrue a \/ IsTrue b -> IsTrue (a || b).
Proof.
  intros a b [Ha | Hb].
  - destruct a; simpl; try apply I; contradiction.
  - destruct a.
    + destruct b; simpl; try apply I; contradiction.
    + destruct b; simpl; try apply I; contradiction.
Qed.

Lemma m_models_l_implies_m_models_l_colon_ls :
  forall (m : Model) (l' : Literal) (ls : list Literal),
  Models_clause m [l'] ->
  Models_clause m (l' :: ls).
Proof.
  intros.
  unfold Models_clause in *.
  apply IsTrue_or_reverse.
  left.
  unfold models_clause in H.
  unfold IsTrue in *.
  destruct (models_literal m l') eqn:Hlit.
  +
  simpl in *.
  auto.
  +
  simpl in *.
  assumption.
Qed.

Lemma models_clause_processListLitsWithLit :
  forall (m : Model) (c : Clause) (l : Literal),
    Models_clause m c ->
    Models_clause m [l] ->
    Models_clause m (removeLitFromClause (negate l) c).
Proof.
  intros m c l Hm_c Hm_neg_l.
  (*destruct c as [ls].*)
  induction c as [| l' ls IHls].
  - (* Base case: c is empty *)
    rewrite processListLitsWithLit_from_empty_clause.
    apply Hm_c.
  - (* Inductive case: c = l' :: ls *)
    destruct (lit_eq_dec l' (negate l)) as [Heq | Hneq].
    + (* Case 1: l' = l *)
      rewrite Heq.
      rewrite remove_l_from_cons_l.
      subst.
      apply IHls.

      revert Hm_neg_l.
      revert Hm_c.
      apply models_ls.
    + (* Case 2: l' != l *)

      unfold models_clause.
      intros.

      pose proof (models_c_implies_models_l_or_ls m l' ls Hm_c) as Hm_c'.

(*      specialize (IHls Hm_c').*)
      destruct Hm_c'.

      (*Case m models consclause l'*)

      (*By lemma 5: remove l (l’:: c’)=    l’ :: remove l c’*)
      pose proof (rewrite_removal (negate l) l' ls Hneq) as H1.

      rewrite H1.

      (*By  models l’ we get  m models ( l’  ::  remove l c’ ) and
      therefore m models  ( remove l (l’ :: c’))*)
      apply m_models_l_implies_m_models_l_colon_ls.
      assumption.

      (* Lemma 5: l not= l' implies remove l (l’ :: c’) = l’ :: (remove l c’)*)
      pose proof (rewrite_removal (negate l) l' ls Hneq) as H1.

      rewrite H1.

      (*m models ( l’  ::  (remove l c’)) (M models ls -> M models l’:ls)*)
      assert (Models_clause m (l' :: remove lit_eq_dec (negate l) ls)).
      *
      apply m_models_ls_implies_m_models_l_colon_ls.

      pose proof IHls H as H_removed.
      rewrite removeLitFromClause_equiv in H_removed.
      exact H_removed.

      * assumption.
Qed.

Lemma SoundnessUres :
  forall (f : Formula) (c : Clause) (l : Literal),
    entails f c ->
    entails f [l] ->
    entails f (removeLitFromClause (negate l) c).
Proof.
  intros f c l.
  intros f_entails_c f_entails_neg_l.

  intros m Hmodel_prop.

  (* Now need to prove that m satisfies c and ¬l *)
  assert (Hm_c: Models_clause m c).
  { apply f_entails_c; assumption. }
  assert (Hm_neg_l: Models_clause m [l]).
  { apply f_entails_neg_l; assumption. }

  destruct c.
  apply models_processListLitsWithLit_from_empty_clause.
  assumption.

  apply models_clause_processListLitsWithLit.
  assumption.
  assumption.
Qed.

Lemma entailmentResolution :
forall (al : Assumption) (c1 c2 : Clause),
  entails al c1 ->
  entails al c2 ->
  is_unit_clause c2 = true ->
  entails al
  (removeLitFromClause
     (negate (ClauseToLiteralWithDefault c2)) c1).
Proof.
  intros.
  apply UnitClauseCorrect in H1.
  rewrite H1 in H0.
  apply SoundnessUres.
  assumption.
  assumption.
Qed.

Lemma SoundnessOfTreeProofs :
forall (al : Assumption) (t : TreeProof) (c : Clause),
  CorrectProof al c t ->
  entails al c.
Proof.
  intros al t.
  induction t.
  -
  intros.
  unfold CorrectProof in H.
  unfold correctConclusion in H.
  unfold findAssumption in H.
  apply nth_error_entails with n. assumption.
  -
  intros.
  assert (X := H).
  apply CorrectProofTrue in X.
  assert (Y' := X).
  apply TP_from_Res_1 in X.
  apply TP_from_Res_2 in Y'.

  unfold CorrectProof in *.

  apply tpCorrectEqualsTrue in X.
  apply tpCorrectEqualsTrue in Y'.

  assert (Y'' := Y').

  assert (X' := X).
  assert (Y := Y').

  apply IHt1 in X.
  apply IHt2 in Y'.

  assert (R := H).
  apply tpCorrectEqualsTrueReverse in R.
  unfold tpCorrect in R.
  simpl in R.
  apply correctConclusionResToUnitClauseTrue in R.
  assert (R' := R).
  apply UnitClauseCorrect in R.
  rewrite Y'' in R.
  unfold OptionClauseToClause in R.

  simpl in H.
  apply correctConclusionResTrue in H.
  rewrite Y'' in H.
  rewrite X' in H.
  simpl in H.

  rewrite H.
  rewrite Y'' in R'.
  simpl in R'.

  apply entailmentResolution.
  assumption.
  assumption.
  assumption.
Qed.

(*--------------------------------------------------------------------------*)

(* Literal and Clause removal comparison *)

(* Function to compare two clauses - lists of literals *)
Fixpoint clause_eqb (c1 c2 : list Literal) : bool :=
  match c1, c2 with
  | [], [] => true
  | l1 :: tl1, l2 :: tl2 => if literal_eqb l1 l2 then clause_eqb tl1 tl2 else false
  | _, _ => false
  end.

(* Function to compare two lists of Clauses (Formulas) *)
Fixpoint formula_eqb (f1 f2 : list Clause) : bool :=
  match f1, f2 with
  | [], [] => true
  | c1 :: cs1, c2 :: cs2 => clause_eqb c1 c2 && formula_eqb cs1 cs2
  | _, _ => false
  end.

(* Function to compare two boolean values *)
Definition bool_eqb (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(* Function to convert a list of literals to a list of single-element clauses *)
Fixpoint literals_to_single_clauses (literals : list Literal) : list Clause :=
  match literals with
  | [] => []
  | l :: ls => [l] :: literals_to_single_clauses ls
  end.

(*Showing removal literal is the same*)
(* Function to compare the outputs of processAndSplitClausesWithLit and processListLitsWithLit *)
Definition compare_outputs (literals : list Literal) (l : Literal) : bool :=
  let result := processAndSplitClausesWithLit (literals_to_single_clauses literals) l in
  let (processed_clauses, unit_literals) := fst result in
  let contains_empty := snd result in
  let (remaining_literals_list, emptylit) := processListLitsWithLit literals l in
  let clauses_eq := formula_eqb processed_clauses [] in
  let literals_eq := clause_eqb unit_literals remaining_literals_list in
  let bool_eq := bool_eqb contains_empty emptylit in
  clauses_eq && literals_eq && bool_eq.

(*
(* Example usage *)
Definition example_literals : list Literal := [pos "a"; neg "b"; pos "c"].
Definition example_literal : Literal := pos "a".
Compute compare_outputs example_literals example_literal.

Definition example_literals2 : list Literal := [neg "a"; neg "b"; pos "c"].
Definition example_literal2 : Literal := pos "a".
Compute compare_outputs example_literals2 example_literal2.
*)

(* #####  from Logical_Entailment.v #### *)

Definition negate_clause (c : Clause) : Formula :=
  map (fun l => [negate l]) c.


Lemma emptyClauseNotModelled : forall (m : Model), ~ Models_clause m [].
Proof.
  intros.
  unfold Models_clause.
  unfold models_clause.
  unfold IsTrue.
  auto.
Qed.

Lemma orFalse1 : forall (b : bool), b || false = b.
Proof.
  intros.
  destruct b.
  auto.
  auto.
Qed.

Lemma doubleNegBool : forall (b : bool), negb (negb b) = b.
Proof.
  intros.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

(* H0 : IsTrue (negb (m s) && models_formula m A) -> False *)
Lemma  notbandb'impliesor :
  forall (b b' : bool),
    (IsTrue (b && b') -> False )
    ->   (IsTrue (negb b)) \/ (IsTrue (negb b')).
Proof.
  intros.
  destruct b.
  unfold andb in H.
  destruct b'.
  unfold IsTrue in H.
  contradiction.
  right.
  simpl.
  auto.
  simpl.
  left.
  auto.
Qed.

Lemma booltopropNegb : forall (b : bool),
    IsTrue (negb b) -> IsTrue b -> False.
Proof.
  intros.
  destruct b.
  simpl in H0.
  assumption.
  simpl in H.
  assumption.
Qed.

Lemma orfalse1 : forall (b : bool), b || false = b.
Proof.
  intros.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma negbBoolLem1 : forall (b : bool),  IsTrue (negb b) -> ~ (IsTrue b).
Proof.
  intros.
  destruct b.
  simpl.
  simpl in H.
  contradiction.
  simpl.
  auto.
Qed.

(* IsTrue (negb (models_formula m A)) *)

Lemma bImplModelsEmptyImpliesNotbaux : forall (b : bool)(m : Model),
    (IsTrue b -> Models_clause m [])
    ->   IsTrue b -> False.
Proof.
  intros.
  apply H in H0.
  apply emptyClauseNotModelled in H0.
  assumption.
Qed.

Lemma bImplModelsEmptyImpliesNotb : forall (b : bool)(m : Model),
    (IsTrue b -> Models_clause m [])
    ->   IsTrue (negb b).
Proof.
  intros.
  pose proof (bImplModelsEmptyImpliesNotbaux b m H) as Ha.
  destruct b.
  simpl in Ha.
  contradiction.
  simpl.
  auto.
Qed.

Lemma m_doesn't_model_falsity :
  forall (m : Model),
  Models_clause m [] ->
  False.
Proof.
  intros.
  unfold Models_clause in H.
  unfold models_clause in H.
  contradiction.
Qed.

Lemma IsTrue_and_reverse : forall a b : bool,
  IsTrue a /\ IsTrue b -> IsTrue (a && b).
Proof.
  intros a b [Ha Hb].
  destruct a, b; simpl; try apply I; try contradiction.
Qed.

Lemma IsTrue_and_equiv : forall a b : bool,
  IsTrue (a && b) <-> IsTrue a /\ IsTrue b.
Proof.
  intros a b.
  split.
  - apply IsTrue_and.
  - apply IsTrue_and_reverse.
Qed.

Lemma modelsAandC : forall (m : Model) (A : Formula)(c : Clause),
Models_formula m A -> Models_formula m [c] ->
Models_formula m ([c] ++ A).
Proof.
  intros.
  unfold Models_formula in *.
  simpl.
  apply IsTrue_and_reverse.
  split.
  unfold models_formula in H0.
  apply IsTrue_and in H0.
  destruct H0 as [H0L H0R].
  assumption.
  assumption.
Qed.

Lemma notmodel : forall (m : Model) (A : Formula)(c : Clause),
Models_formula m A ->
~ Models_formula m ([c] ++ A) ->
~ Models_formula m [c].
Proof.
  intros.
  intro.
  apply modelsAandC with m A c in H1.
  contradiction.
  assumption.
Qed.

Lemma IsTrue_or : forall a b : bool,
  IsTrue (a || b) -> IsTrue a \/ IsTrue b.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try (left; apply I); try (right; apply I); try contradiction.
Qed.

Lemma Models_formula_opposite : forall (m : Model) (x : Literal),
  ~ Models_formula m [[negate x]] -> Models_formula m [[x]].
Proof.
  intros m x H.
  unfold Models_formula in *.
  unfold models_formula in *.
  apply IsTrue_and_reverse.

  unfold IsTrue in *.
  simpl in *.
  unfold models_literal in *.
  destruct x as [a | a]; simpl in *.
  - (* Case: x = pos a *)
    unfold negate in H. simpl in H.
    destruct (m a). simpl in *. try contradiction. split. auto. auto.
    simpl in *. try contradiction.
  - (* Case: x = neg a *)
    unfold negate in H. simpl in H.
    destruct (m a). simpl in *. try contradiction.
    simpl in *. try contradiction. split. auto. auto.
Qed.


(* ##########################  Proofs of entailsFalsity1, 2, 3 ############### *)
(*Lemma 1*)
Lemma entailsFalsity1 : forall (A : Formula) (c : Clause) (x : Literal),
  entails ([[negate x]] ++ A) [] -> entails A [x].
Proof.
  intros A c x Hentails.
  unfold entails in *.
  intros.
  specialize (Hentails m).

  unfold Models_clause.
  unfold models_clause.
  apply IsTrue_or_reverse.
  left.

  assert (Hnot_models : ~ Models_formula m ([[negate x]] ++ A)).
    {
      intros Hmodels.
      apply m_doesn't_model_falsity with (m := m).
      apply Hentails. (* Using Hentails to derive models_clause m [] *)
      exact Hmodels.
    }

  apply notmodel in Hnot_models.
  +
    apply Models_formula_opposite in Hnot_models.
    unfold Models_formula in Hnot_models.
    unfold models_formula in Hnot_models.
    apply IsTrue_and in Hnot_models.
    destruct Hnot_models as [nmL nmR].
    unfold models_clause in nmL.
    apply IsTrue_or in nmL.
    destruct nmL as [nmLL | nmLR].
    assumption.
    contradiction.
  +
    assumption.
Qed.

(*---------------------------------------------------------------------*)

Lemma models_formula_cons_general : forall (m : Model) (A B : Formula),
  Models_formula m (A ++ B) -> Models_formula m A /\ Models_formula m B.
Proof.
  intros m A B H.
  unfold Models_formula in *.
  induction A as [| a A' IHA].
  - simpl in *. split.
    + apply I.
    + exact H.
  - simpl in H. apply IsTrue_and in H. destruct H as [H1 H2].
    specialize (IHA H2). destruct IHA as [HA HB].
    split.
    + unfold Models_formula. simpl. apply IsTrue_and_reverse. split.
      * exact H1.
      * exact HA.
    + exact HB.
Qed.

Lemma models_formula_append : forall (m : Model) (A B : Formula),
  Models_formula m A -> Models_formula m B -> Models_formula m (A ++ B).
Proof.
  intros m A B H_A H_B.
  unfold Models_formula in *.
  induction A as [| a A' IHA].
  - simpl. exact H_B.
  - simpl. apply IsTrue_and_reverse. split.
    + apply IsTrue_and in H_A. destruct H_A as [H_a H_A'].
      exact H_a.
    + apply IHA.
      apply IsTrue_and in H_A. destruct H_A as [H_a H_A'].
      exact H_A'.
Qed.

Lemma models_formula_split : forall (m : Model) (A : Formula) (B : Clause),
  Models_formula m ([B] ++ A) -> Models_formula m [B] /\ Models_formula m A.
Proof.
  intros m A B H.
  unfold Models_formula in *.
  unfold IsTrue in *.
  simpl in H.
  apply IsTrue_and in H.
  destruct H as [H_B H_A].
  split.
  - unfold Models_formula. unfold IsTrue. simpl. apply IsTrue_and_reverse. split.
    + assumption.
    + simpl. auto.
  - assumption.
Qed.

Lemma models_formula_implies_clause : forall (m : Model) (A : Formula) (B : Clause) (C : Clause),
  (Models_formula m A -> Models_clause m C) /\
  (Models_formula m [B] -> Models_clause m C) ->
  Models_formula m ([B] ++ A) ->
  Models_clause m C.
Proof.
  intros m A B C [H1 H2] H3.
  apply models_formula_split in H3.
  destruct H3 as [H3B H3A].
  apply H1 in H3A.
  apply H2 in H3B.
  assumption.
Qed.

Lemma xs_in_A_implies_models_clause : forall (m : Model) (A : Formula) (xs : Clause),
  In xs A -> Models_formula m A -> Models_clause m xs.
Proof.
  intros m A xs HinA HmodelsA.
  unfold Models_formula in HmodelsA.
  induction A as [| h t IH].
  - simpl in HinA. contradiction.
  - simpl in HmodelsA. simpl in HinA.
    apply IsTrue_and in HmodelsA.
    destruct HmodelsA as [Hh Ht].
    destruct HinA as [HinH | HinT].
    + rewrite HinH in Hh.
      unfold Models_clause.
      destruct (models_clause).
      assumption.
      assumption.
    + apply IH in HinT.
      * unfold Models_clause.
        destruct (models_clause).
        unfold Models_clause in HinT.
        assumption.
        unfold Models_clause in HinT.
        assumption.
      * destruct (models_formula).
        assumption.
        assumption.
Qed.

Lemma xs_in_A_B_implies_models : forall (m : Model) (A : Formula) (B : Clause) (xs : Clause),
  In xs ([B] ++ A) -> (Models_formula m ([B] ++ A) -> Models_clause m xs).
Proof.
  intros m A B xs Hin Hmodels.
  (* Use the hypothesis Hin to handle the cases where xs is B or xs is in A *)
  apply in_app_or in Hin.
  destruct Hin as [HinB | HinA].
  - (* Case: xs is B *)
    unfold Models_formula in Hmodels.
    simpl in Hmodels.
    apply IsTrue_and in Hmodels.

    destruct Hmodels as [HmL HmR].
    unfold Models_clause.
    unfold In in HinB.
    destruct HinB.
    rewrite <- H.
    assumption.
    contradiction.
  - (* Case: xs is in A *)
    apply models_formula_split with m A B in Hmodels.
    destruct Hmodels as [HmL HmR].
    unfold Models_formula in HmR.
    unfold Models_clause.
    apply xs_in_A_implies_models_clause with A.
    + assumption.
    + unfold Models_formula.
      assumption.
Qed.

Lemma models_formula_clause_split : forall (m : Model) (A : Formula) (B : Clause) (C : Clause),
  Models_formula m ([B] ++ A) ->
  Models_clause m C ->
  (Models_formula m [B] -> Models_clause m C) /\
  (Models_formula m A -> Models_clause m C).
Proof.
  intros m A B C Hmodels Hclause.
  split.
  -
    intros HmodelsA.
    assumption.
  -
    intros HmodelsB.
    assumption.
Qed.

Lemma models_clause_cons : forall (m : Model) (x : Literal) (xs : Clause),
  Models_literal m x \/ Models_clause m xs -> Models_clause m (x :: xs).
Proof.
  intros m x xs H.
  unfold Models_clause.
  simpl.
  destruct H as [Hlit | Hclause].
  - (* Case: Models_literal m x *)
    unfold Models_literal in Hlit.
    apply IsTrue_or_reverse.
    left.
    assumption.
  - (* Case: Models_clause m xs *)
    unfold Models_clause in Hclause.
    apply IsTrue_or_reverse.
    right.
    assumption.
Qed.

Lemma models_clause_cons_reverse : forall (m : Model) (x : Literal) (xs : Clause),
  Models_clause m (x :: xs) -> Models_literal m x \/ Models_clause m xs.
Proof.
  intros m x xs H.
  unfold Models_clause in H.
  simpl in H.
  apply IsTrue_or in H.
  destruct H as [Hlit | Hclause].
  - (* Case: Models_literal m x *)
    left.
    unfold Models_literal.
    assumption.
  - (* Case: Models_clause m xs *)
    right.
    unfold Models_clause.
    assumption.
Qed.

Lemma simplify_false : forall (m : Model) (a : Pos_Z3_Formula) (A : Formula) (B : bool)
(xs : Clause),
  (IsTrue ((B || false) && models_formula m A) -> Models_clause m xs) ->
  (IsTrue (B && models_formula m A) -> Models_clause m xs).
Proof.
  intros m a A B xs Hentails H.
  simpl in H.
  apply Hentails.
  apply IsTrue_and_reverse.
  split.
  apply IsTrue_or_reverse.
  apply IsTrue_and in H.
  destruct H as [HL HR].
  left.
  assumption.
  apply IsTrue_and in H.
  destruct H as [HL HR].
  assumption.
Qed.

Lemma simplify_false_reverse : forall (m : Model) (a : Pos_Z3_Formula) (A : Formula) 
(B : bool) (xs : Clause),
  (IsTrue (B && models_formula m A) -> Models_clause m xs) ->
  (IsTrue ((B || false) && models_formula m A) -> Models_clause m xs).
Proof.
  intros m a A B xs Hentails H.
  simpl in H.
  (* Simplify the expression (negb (m a) || false) to negb (m a) *)
  rewrite orb_false_r in H.
  (* Now apply the original hypothesis Hentails *)
  apply Hentails.
  assumption.
Qed.

Lemma simplify_falsity_equivalence : forall (m : Model) (a : Pos_Z3_Formula) 
(A : Formula) (B : bool) (xs : Clause),
  (IsTrue ((B || false) && models_formula m A) -> Models_clause m xs) <->
  (IsTrue (B && models_formula m A) -> Models_clause m xs).
Proof.
  intros m a A B xs.
  split.
  - apply simplify_false. assumption.
  - apply simplify_false_reverse. assumption.
Qed.

Lemma and_implication : forall A B C : Prop,
  (A /\ B -> C) -> B -> (A -> C).
Proof.
  intros A B C H H_B H_A.
  apply H.
  split.
  - apply H_A.
  - apply H_B.
Qed.

Lemma and_implication_equiv : forall A B C : Prop,
  (A /\ B -> C) <-> (B -> A -> C).
Proof.
  intros A B C.
  split.
  - intros H H_B H_A.
    apply H.
    split.
    + apply H_A.
    + apply H_B.
  - intros H [H_A H_B].
    apply H.
    + apply H_B.
    + apply H_A.
Qed.


(*Lemma 2*)
Lemma entailsFalsity2 : forall (A : Formula) (c : Clause) (x : Literal) (xs : Clause),
  entails ([[negate x]] ++ A) xs -> entails A (x :: xs).
Proof.
  intros A c x xs Hentails.
  unfold entails in *.
  intros m Hmodels.
  specialize (Hentails m).

  apply models_clause_cons.
  destruct x.
  +
  unfold Models_literal.

  unfold models_literal.
  unfold Models_formula in Hentails.

  simpl in Hentails.
  rewrite simplify_falsity_equivalence in Hentails.
  rewrite IsTrue_and_equiv in Hentails.
  unfold Models_formula in Hmodels.

  destruct (m p) eqn:Hma.
  left.
  simpl in *.
  exact I.
  right.
  apply Hentails.
  split.
  simpl in *.
  exact I.
  assumption.
  assumption.
  +
  unfold Models_literal.

  unfold models_literal.
  unfold Models_formula in Hentails.

  simpl in Hentails.
  rewrite simplify_falsity_equivalence in Hentails.
  rewrite IsTrue_and_equiv in Hentails.
  unfold Models_formula in Hmodels.

  destruct (m p) eqn:Hma.
  right.
  apply Hentails.
  split.
  simpl in *.
  exact I.
  assumption.
  left.
  simpl in *.
  exact I.
  assumption.
Qed.

Lemma Models_formula_empty_clause : forall (m : Model),
  ~ Models_formula m [[]].
Proof.
  intros m H.
  unfold Models_formula in H.
  simpl in H.
  unfold Models_clause in H.
  simpl in H.
  contradiction.
Qed.

Lemma nil_app_eq : forall (A : list Clause),
  [] ++ A = A.
Proof.
  intros A.
  simpl.
  reflexivity.
Qed.

Lemma cons_nil_app_eq : forall (A : list (list Clause)),
  [[]] ++ A = [] :: A.
Proof.
  intros A.
  simpl.
  reflexivity.
Qed.

Lemma cons_app_eq : forall (A : Clause) (B : list Clause),
  [A] ++ B = A :: B.
Proof.
  intros A B.
  simpl.
  reflexivity.
Qed.

Lemma Models_formula_cons_empty : forall (m : Model) (A : Formula),
  Models_formula m A -> Models_formula m ([] ++ A).
Proof.
  intros m A H.
  unfold Models_formula in *.
  unfold IsTrue in *.
  simpl.
  assumption.
Qed.

Lemma not_False_is_True : ~ False <-> True.
Proof.
  split.
  - (* ~ False -> True *)
    intros H. exact I.
  - (* True -> ~ False *)
    intros H. intro. contradiction.
Qed.

(*Lemma 3*)
Lemma entailsFalsity : forall (A : Formula) (xs : Clause),
  entails (negate_clause xs ++ A) [] -> entails A xs.
Proof.
  intros A xs H.
  unfold entails in *.
  intros m Hm.
  specialize (H m).
  unfold Models_formula in *.
  simpl in *.
  unfold models_clause in *.
  unfold models_literal in *.
  (* Assume that negate_clause xs ++ A is unsatisfiable *)
  assert (H1: ~ Models_formula m (negate_clause xs ++ A)).
  { intro H1. apply H. assumption. }
  (* Show that A entails xs *)
  unfold Models_clause.
  unfold models_clause.
  induction xs as [| x xs' IH].
  - (* Base case: xs is empty *)
    simpl in *. apply m_doesn't_model_falsity with m. apply H. assumption.
  - (* Inductive step: xs is non-empty *)
    simpl in *.
    destruct x as [a | a]; simpl in *.
    + (* Case: x = pos a *)
      unfold negate in H1. simpl in H1.
      destruct (m a) eqn:Ha; simpl in *; try contradiction.
      * (* Subcase: m a = true *)
        split; auto.
      * (* Subcase: m a = false *)
        auto.
    + (* Case: x = neg a *)
      unfold negate in H1. simpl in H1.
      destruct (m a) eqn:Ha; simpl in *; try contradiction.
      * (* Subcase: m a = true *)
        auto.
      * (* Subcase: m a = false *)
        split; auto.
Qed.

Lemma CorrectOptionTreeProofToEntails:
  forall (al : Assumption)(b : bool)(t : option TreeProof),
    b = true
    -> CorrectOptionTreeProof' al b t
    -> entails al [].
Proof.
  intros.
  rewrite H in H0.
  destruct t.
  unfold CorrectOptionTreeProof' in H0.
  apply (SoundnessOfTreeProofs al t []).
  assumption.
  unfold CorrectOptionTreeProof' in H0.
  contradiction.
Qed.

(* ############################  Main RUP Checker ############################ *)
(* RUP_Checker *)
Definition RUP_Checker (a : Assumption) (c : Clause) : bool :=
  unitPropagationAndCheck ((negate_clause c) ++ a).

Definition RUP_CheckerProof (a : Assumption) (c : Clause) : option TreeProof :=
  unitPropagationAndCheckWithAssProof ((negate_clause c) ++ a).


Lemma RUP_CheckerProofCorrect : forall (a : Assumption) (c : Clause),
    CorrectOptionTreeProof (negate_clause c ++ a) (RUP_Checker a c)
     (RUP_CheckerProof a c).
Proof.
  intros.
  unfold RUP_Checker, RUP_CheckerProof.
  apply unitPropagationAndCheckWithAssCorrect.
Qed.

Lemma RUP_to_entailsFalsity :
  forall (a : Assumption) (c : Clause),
    RUP_Checker a c = true
    -> entails (negate_clause c ++ a) [].
Proof.
intros.
apply (CorrectOptionTreeProofToEntails (negate_clause c ++ a) (RUP_Checker a c) (RUP_CheckerProof a c)).
assumption.
apply CorrectOpenTreeProofEquiv2.
apply  RUP_CheckerProofCorrect.
Qed.


(* Main Theorem *)
Lemma RUP_Checker_correct :
  forall (a : Assumption)(c : Clause),
    RUP_Checker a c = true -> entails a c.
Proof.
  intros a c Hrup.
  apply entailsFalsity.
  apply RUP_to_entailsFalsity.
  assumption.
Qed.

(*--------------------------------------------------------------------------*)

Fixpoint Zfor2Lit (f : Z3_Formula) : Literal :=
  match f with
  | not x =>
      match x with
      | z3var v => neg (pos_z3var v)
      | and l => neg (pos_and l)
      | or l => neg (pos_or l)
      | imply a b => neg (pos_imply a b)
      | not y => Zfor2Lit y  (* double negation elimination *)
      end
  | z3var v => pos (pos_z3var v)
  | and l => pos (pos_and l)
  | or l => pos (pos_or l)
  | imply a b => pos (pos_imply a b)
  end.

(* Convert a single ZClause to an RClause *)
Fixpoint zCl2RClause (zc : ZClause) : Clause :=
  match zc with
  | lnil => []
  | lcons x xs => Zfor2Lit x :: zCl2RClause xs
  end.

Definition ZProof2AssumptionR (p : ZProof) : list Clause :=
  map zCl2RClause (ZProof2Assumption p).

(* Convert a list of ZClauses to a list of RClauses *)
Fixpoint zListCl2RListCl (zcs : list ZClause) : list Clause :=
  match zcs with
  | [] => []
  | x :: xs => zCl2RClause x :: zListCl2RListCl xs
  end.

Fixpoint ZProof2ConclusionOpt (p : ZProof) : list ZClause :=
  match p with
  | [] => []
  | x :: xs => ZProofItem2ConclusionOpt x :: ZProof2ConclusionOpt xs
  end.

Definition ZProof2RupConclusions (p : ZProof) : list Clause :=
  zListCl2RListCl (ZProof2ConclusionOpt p).

Fixpoint in_listZ3b(x : Z3_Formula)(l : listZ3_Formula): bool :=
  match l with
  | lnil=> false
  | lcons y ys=> z3_formula_eq x y || in_listZ3b x ys
  end.

Fixpoint listZ3_subset(l1 l2 : listZ3_Formula): bool :=
  match l1 with
  | lnil=> true
  | lcons x xs=> in_listZ3b x l2 && listZ3_subset xs l2
  end.

Fixpoint negSingletons(l : listZ3_Formula): list listZ3_Formula :=
  match l with
  | lnil=> []
  | lcons f rest=>(lcons(negFor f)lnil):: negSingletons rest
  end.

Fixpoint in_listZ3List(x : listZ3_Formula)(l : list listZ3_Formula): bool :=
  match l with
  | []=> false
  | y :: ys=> list_z3_formula_eq x y || in_listZ3List x ys
  end.

Fixpoint listZ3List_subset(l1 l2 : list listZ3_Formula): bool :=
  match l1 with
  | []=> true
  | x :: xs=> in_listZ3List x l2 && listZ3List_subset xs l2
  end.

Fixpoint setminus(a b : listZ3_Formula): listZ3_Formula :=
  match a with
  | lnil=> lnil
  | lcons x xs=>
      if in_listZ3b x b then
        setminus xs b
      else
        lcons x(setminus xs b)
  end.

Definition ZProofCheckTseitin (item : TseitinStep) : bool :=
  match item with
  | tseitinAndElim l i => Nat.ltb i (length_listZ3 l)
  | tseitinOrIntro l i => Nat.ltb i (length_listZ3 l)
  | _ => true
  end.

Definition ZProofCheckLastStep (cl : list ZClause) (item : ZProofItem) : bool :=
  match item with
  | tseitinStep a => ZProofCheckTseitin a
  | rupZ3proof l => RUP_Checker (zListCl2RListCl cl) (zCl2RClause l)
  | tseitinStepRed a c => listZ3_subset c (TseitinProofItem2ConclusionOpt a) 
                         && listZ3List_subset 
                            (negSingletons (setminus (TseitinProofItem2ConclusionOpt a) c)) cl
                         && ZProofCheckTseitin a
  | _ => true
  end.

Fixpoint ZProofCheck (p : ZProof) : bool :=
  match p with
  | [] => true
  | x :: xs => andb (ZProofCheckLastStep (ZProof2ConclusionOpt xs) x) (ZProofCheck xs)
  end.

Definition isEmpty_listZ3_Formula (l : ZClause) : bool :=
  match l with
  | lnil => true
  | _ => false
  end.

Fixpoint containsEmpty_listZ3 (fs : list ZClause) : bool :=
  match fs with
  | nil => false
  | f :: fs' => if isEmpty_listZ3_Formula f then true else containsEmpty_listZ3 fs'
  end.

Definition ZProofCheckUnsat (l : ZProof) : bool :=
  andb (ZProofCheck l) (containsEmpty_listZ3 (ZProof2ConclusionOpt l)).

(*--------------------------------------------------------------------------*)

(* Define model as a function type from atom to bool *)
Definition ZModel := Z3_Variable -> bool.

(* Evaluate a variable under a model *)
Definition evalZVar (modl : ZModel) (v : Z3_Variable) : bool :=
  modl v.

Definition atom (b : bool) : Prop := b = true.

(* Lift the evaluation result into a logical proposition *)
Definition EvalZVar (modl : ZModel) (v : Z3_Variable) : Prop :=
  atom (evalZVar modl v).

(* Boolean implication *)
Definition implb (a b : bool) : bool := orb (negb a) b.

(* Conjunction over a list of bools *)
Fixpoint andListBool (l : list bool) : bool :=
  match l with
  | [] => true
  | b :: bs => andb b (andListBool bs)
  end.

(* Disjunction over a list of bools *)
Fixpoint orListBool (l : list bool) : bool :=
  match l with
  | [] => false
  | b :: bs => orb b (orListBool bs)
  end.

(* Evaluate a ZFor formula under a model *)
Fixpoint evalZFor (modl : ZModel) (f : Z3_Formula) : bool :=
  match f with
  | z3var v => evalZVar modl v
  | and l => andListBool (evalListZFor modl l)
  | or l => orListBool (evalListZFor modl l)
  | imply f1 f2 => implb (evalZFor modl f1) (evalZFor modl f2)
  | not f1 => negb (evalZFor modl f1)
  end

(* Evaluate a list of ZFor formulas *)
with evalListZFor (modl : ZModel) (l : ZClause) : list bool :=
  match l with
  | lnil => []
  | lcons f rest => evalZFor modl f :: evalListZFor modl rest
  end.

(* Evaluate a ZClause (listZ3_Formula) under a model *)
Definition evalZClause (modl : ZModel) (l : ZClause) : bool :=
  orListBool (evalListZFor modl l).

(* Lift clause evaluation to a proposition *)
Definition EvalZClause (modl : ZModel) (l : ZClause) : Prop :=
  atom (evalZClause modl l).

(* Evaluate a list of ZClauses (list of listZ3_Formula) under a model *)
Fixpoint evalListZClause (modl : ZModel) (l : list ZClause) : bool :=
  match l with
  | [] => true
  | c :: cs => andb (evalZClause modl c) (evalListZClause modl cs)
  end.

(* Lift list of clauses to a proposition *)
Definition EvalListZClause (modl : ZModel) (l : list ZClause) : Prop :=
  atom (evalListZClause modl l).

(*--------------------------------------------------------------------------*)

(* Convert a ZModel to an RModel by evaluating Z3 formulas *)
Definition zModel2Rmodel (modl : Z3_Variable -> bool) : Pos_Z3_Formula -> bool :=
  fun pf => evalZFor modl (match pf with
                         | pos_z3var v => z3var v
                         | pos_and l => and l
                         | pos_or l => or l
                         | pos_imply f1 f2 => imply f1 f2
                         end).

Definition evalRLit (modl : Pos_Z3_Formula -> bool) (l : Literal) : bool :=
  match l with
  | pos pf => modl pf
  | neg pf => negb (modl pf)
  end.

Lemma Zfor2Lit_not_not :
  forall f : Z3_Formula,
    Zfor2Lit (not f) = match f with
                       | not y => Zfor2Lit y
                       | _ => Zfor2Lit (not f)
                       end.
Proof.
  intros f.
  destruct f; simpl; reflexivity.
Qed.

Lemma evalZFor_negb_negb :
  forall modl f', negb (negb (evalZFor modl f')) = evalZFor modl f'.
Proof.
  intros modl f'.
  destruct (evalZFor modl f'); simpl; reflexivity.
Qed.

Lemma negRLitEval1 :
  forall (modl : Pos_Z3_Formula -> bool) (l : Literal),
    evalRLit modl (negate l) = negb (evalRLit modl l).
Proof.
  intros modl l.
  destruct l as [pf | pf]; simpl.
  - (* Case: pos pf *)
    (* negRLit (pos pf) = neg pf, so evalRLit = negb (modl pf) *)
    (* RHS = negb (evalRLit modl (pos pf)) = negb (modl pf) *)
    reflexivity.
  - (* Case: neg pf *)
    (* negRLit (neg pf) = pos pf, so evalRLit = modl pf *)
    (* RHS = negb (evalRLit modl (neg pf)) = negb (negb (modl pf)) *)
    simpl. rewrite Bool.negb_involutive. reflexivity.
Qed.

(*--------------------------------------------------------------------------*)

Definition ZTaut (c : ZClause) : Prop :=
  forall (modl : ZModel), evalZClause modl c = true.

Definition EntailsZCl (ass : list ZClause) (c : ZClause) : Prop :=
  forall (modl : ZModel), evalListZClause modl ass = true -> evalZClause modl c = true.

Definition entailsAddTaut' 
  (c : ZClause) 
  (ctaut : ZTaut c) 
  (ass : list ZClause) 
  : EntailsZCl ass c :=
  fun (modl : ZModel) (_ : evalListZClause modl ass = true) => ctaut modl.

Definition EntailsListZCl (ass f : list ZClause) : Prop :=
  forall (modl : ZModel), EvalListZClause modl ass -> EvalListZClause modl f.

Lemma andb_intro : forall a b : bool,
  a = true -> b = true -> andb a b = true.
Proof.
  intros a b Ha Hb.
  rewrite Ha, Hb.
  reflexivity.
Qed.

(*--------------------------------------------------------------------------*)

Fixpoint mapListZ (f : Z3_Formula -> bool) (l : listZ3_Formula) : list bool :=
  match l with
  | lnil => nil
  | lcons x xs => f x :: mapListZ f xs
  end.

Lemma notNegForEq : forall (modl : ZModel) (x : Z3_Formula),
  evalZFor modl (not x) = negb (evalZFor modl x).
Proof.
  intros modl x.
  simpl.
  reflexivity.
Qed.

Fixpoint negListZ3 (l : listZ3_Formula) : listZ3_Formula :=
  match l with
  | lnil => lnil
  | lcons f rest => lcons (not f) (negListZ3 rest)
  end.

Lemma negForListEq : forall (modl : ZModel) (l : listZ3_Formula),
  evalListZFor modl (negListZ3 l) = map negb (evalListZFor modl l).
Proof.
  intros modl l.
  induction l as [| f rest IH].
  - (* Base case: lnil *)
    simpl. reflexivity.
  - (* Inductive case: lcons f rest *)
    simpl.
    rewrite <- notNegForEq.
    rewrite IH.
    reflexivity.
Qed.

(*--------------------------------------------------------------------------*)

(* Tautologies *)

(* Not Case *)
 
Lemma tseitinNotTautaux : forall a : bool,
  orb a (orb (negb a) false) = true.
Proof.
  intros a.
  destruct a; simpl; reflexivity.
Qed.

Lemma tseitinNotTautaux' : forall a : bool,
  orListBool [a; (negb a)] = true.
Proof.
  intros a.
  destruct a; simpl; reflexivity.
Qed.

Lemma negForCorrect : forall modl x,
  evalZFor modl (negFor x) = negb (evalZFor modl x).
Proof.
  intros modl x.
  unfold negFor.
  destruct x; simpl; try reflexivity.
  rewrite doubleNegBool. reflexivity.
Qed.

Lemma tseitinNotTaut : forall (x : Z3_Formula),
  ZTaut (tseitinNot2For x).
Proof.
  intros x modl.
  unfold ZTaut, tseitinNot2For.
  unfold evalZClause.
  simpl.

  rewrite negForCorrect.
  apply tseitinNotTautaux.
Qed.

(* Imp Elim *)

Definition tseitinImpElimTautaux (x y : bool) : bool :=
  orb (negb x) (orb y (orb (negb (orb (negb x) y)) false)).

Lemma tseitinImpElimTautaux_true : forall x y : bool,
  tseitinImpElimTautaux x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Lemma tseitinImpElimTaut : forall (x y : Z3_Formula),
  ZTaut (tseitinImpElim2For x y).
Proof.
  intros x y m.
  unfold ZTaut, tseitinImpElim2For.
  unfold evalZClause.
  simpl.
  rewrite negForCorrect.
  apply tseitinImpElimTautaux_true.
Qed.

(* Imp Intro 1 *)

Definition tseitinImpIntro1Tautaux (x y : bool) : bool :=
  orb x (orb (orb (negb x) y) false).

Lemma tseitinImpIntro1Tautaux_true : forall x y : bool,
  tseitinImpIntro1Tautaux x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Lemma tseitinImpIntro1Taut : forall (x y : Z3_Formula),
  ZTaut (tseitinImpIntro1toFor x y).
Proof.
  intros x y m.
  unfold ZTaut, tseitinImpIntro1toFor.
  unfold evalZClause.
  simpl.
  apply tseitinImpIntro1Tautaux_true.
Qed.

(* Imp Intro 2 *)

Definition tseitinImpIntro2Tautaux (x y : bool) : bool :=
  orb (negb y) (orb (orb (negb x) y) false).

Lemma tseitinImpIntro2Tautaux_true : forall x y : bool,
  tseitinImpIntro2Tautaux x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Lemma tseitinImpIntro2Taut : forall (x y : Z3_Formula),
  ZTaut (tseitinImpIntro2toFor x y).
Proof.
  intros x y m.
  unfold ZTaut, tseitinImpIntro2toFor.
  unfold evalZClause.
  simpl.
  rewrite negForCorrect.
  apply tseitinImpIntro2Tautaux_true.
Qed.

(* Imp Intro 3 *)

Definition tseitinImpIntro3Tautaux (x y : bool) : bool :=
  orb (negb y) (orb (orb (negb x) y) false).

Lemma tseitinImpIntro3Tautaux_true : forall x y : bool,
  tseitinImpIntro3Tautaux x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Lemma tseitinImpIntro3Taut : forall (x y : Z3_Formula),
  ZTaut (tseitinImpIntro3toFor x y).
Proof.
  intros x y m.
  unfold ZTaut, tseitinImpIntro3toFor.
  unfold evalZClause.
  simpl.
  apply tseitinImpIntro3Tautaux_true.
Qed.

(* And Intro *)

Definition tseitinAndIntroTautaux (l : list bool) : bool :=
  orb (andListBool l) (orListBool (map negb l)).

Lemma tseitinAndIntroTautaux_true : forall l : list bool,
  tseitinAndIntroTautaux l = true.
Proof.
  induction l as [| b rest IH].
  - reflexivity.
  - destruct b.
    + apply IH.
    + cbn. reflexivity.
Qed.

Lemma evalListZFor_negForList : forall (modl : ZModel) (l : ZClause),
  evalListZFor modl (negForList l) = map negb (evalListZFor modl l).
Proof.
  intros modl l.
  induction l as [| f rest IH].
  - simpl. reflexivity.
  - simpl. rewrite negForCorrect. rewrite IH. reflexivity.
Qed.

Lemma tseitinAndIntroTaut : forall (l : ZClause),
  ZTaut (tseitinAndIntro2ForOpt l).
Proof.
  intros l m.
  unfold ZTaut, tseitinAndIntro2ForOpt.
  unfold evalZClause.
  simpl.
  rewrite evalListZFor_negForList.
  apply tseitinAndIntroTautaux_true.
Qed.

(* And Elim *)

Definition tseitinAndElimTautaux1 (x y : bool) : bool :=
  orb x (orb (negb (andb x y)) false).

Lemma tseitinAndElimTautaux1_true : forall x y : bool,
  tseitinAndElimTautaux1 x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Definition tseitinAndElimTautaux2 (x y z : bool) : bool :=
  orb x (orb (negb (andb y z)) false).

Lemma tseitinAndElimTautaux2_true : forall x y z : bool,
  orb x (orb (negb z) false) = true ->
  tseitinAndElimTautaux2 x y z = true.
Proof.
  intros x y z H.
  destruct x, y, z; simpl; auto.
Qed.

Require Import Lia.

Lemma tseitinAndElimTaut : forall (l : ZClause) (i : nat),
  i < length_listZ3 l ->
  ZTaut (tseitinAndElim2For l i).
Proof.
  induction l as [| x l' IH]; intros i Hlt m.
  - simpl in Hlt. lia. (* i < 0 is impossible *)
  - destruct i as [| i'].
    + simpl. apply tseitinAndElimTautaux1_true.
    + simpl.
      apply tseitinAndElimTautaux2_true.
      apply IH.
      apply Nat.lt_succ_r. exact Hlt.
Qed.

(* Or Intro *)

Definition tseitinOrIntroTautaux1 (x y : bool) : bool :=
  orb (negb x) (orb (orb x y) false).

Lemma tseitinOrIntroTautaux1_true : forall x y : bool,
  tseitinOrIntroTautaux1 x y = true.
Proof.
  intros x y.
  destruct x, y; simpl; reflexivity.
Qed.

Definition tseitinOrIntroTautaux2 (x y z : bool) : bool :=
  orb x (orb (orb z y) false).

Lemma tseitinOrIntroTautaux2_true : forall x y z : bool,
  orb x (orb y false) = true ->
  tseitinOrIntroTautaux2 x y z = true.
Proof.
  intros x y z H.
  destruct x, y, z; simpl; auto.
Qed.

Lemma tseitinOrIntroTaut : forall (l : ZClause) (i : nat),
  i < length_listZ3 l ->
  ZTaut (tseitinOrIntro2For l i).
Proof.
  induction l as [| x l' IH]; intros i Hlt m.
  - simpl in Hlt. lia.
  - destruct i as [| i'].
    + cbn.
      rewrite negForCorrect.
      apply tseitinOrIntroTautaux1_true.
    + cbn.
      apply tseitinOrIntroTautaux2_true.
      apply IH.
      apply Nat.lt_succ_r. exact Hlt.
Qed.

(* Or Elim *)

Definition tseitinOrElimTautaux (l : list bool) : bool :=
  orb (negb (orListBool l)) (orListBool l).

Lemma tseitinOrElimTautaux_true : forall l : list bool,
  tseitinOrElimTautaux l = true.
Proof.
  intros l.
  unfold tseitinOrElimTautaux.
  destruct (orListBool l) eqn:H.
  - (* Case: orListBool l = true *)
    simpl. reflexivity.
  - (* Case: orListBool l = false *)
    simpl. reflexivity.
Qed.

Lemma tseitinOrElimTaut : forall (l : ZClause),
  ZTaut (tseitinOrElim2ForOpt l).
Proof.
  intros l m.
  unfold ZTaut, tseitinOrElim2ForOpt.
  unfold evalZClause.
  simpl.
  apply tseitinOrElimTautaux_true.
Qed.

(*--------------------------------------------------------------------------*)

Lemma entailsAddTaut :
  forall (c : ZClause) (cl as_ : list ZClause),
    ZTaut c ->
    EntailsListZCl as_ cl ->
    EntailsListZCl as_ (c :: cl).
Proof.
  intros c cl as_ Htaut Hentails modl Heval.
  unfold EntailsListZCl in Hentails.
  unfold ZTaut in Htaut.
  simpl.
  (* We need to show that evalZClause modl c = true 
     and all clauses in cl evaluate to true *)
  apply andb_true_intro.
  split.
  - apply Htaut.
  - apply Hentails. assumption.
Qed.

Lemma entailsAddEntails :
  forall (c : ZClause) (cl as_ : list ZClause),
    EntailsZCl as_ c ->
    EntailsListZCl as_ cl ->
    EntailsListZCl as_ (c :: cl).
Proof.
  intros c cl as_ Hc Hcl modl Hass.

  unfold EntailsListZCl in Hcl.
  unfold EntailsZCl in Hc.
  unfold EvalListZClause.

  simpl.
  (* Use both entailments *)
  apply andb_true_intro.
  split.
  - apply Hc. exact Hass.
  - apply Hcl. exact Hass.
Qed.

Lemma andb_elim1 : forall (b1 b2 : bool),
  IsTrue (andb b1 b2) -> IsTrue b1.
Proof.
  intros b1 b2 H.
  unfold IsTrue in *.
  simpl in H.
  destruct b1, b2; simpl in *; try discriminate; auto.
Qed.

Lemma andb_elim2 : forall (b1 b2 : bool),
  IsTrue (andb b1 b2) -> IsTrue b2.
Proof.
  intros b1 b2 H.
  unfold IsTrue in *.
  simpl in H.
  destruct b1, b2; simpl in *; try discriminate; auto.
Qed.

Lemma IsTrue_andb_split :
  forall b1 b2 : bool,
    IsTrue (andb b1 b2) -> IsTrue b1 /\ IsTrue b2.
Proof.
  intros b1 b2 H.
  unfold IsTrue in H.
  destruct b1, b2; simpl in H; try contradiction; split; trivial.
Qed.

Lemma entailsAddAssumption :
  forall (c : ZClause) (z : list ZProofItem),
    EntailsListZCl (ZProof2Assumption z) (ZProof2ConclusionOpt z) ->
    EntailsListZCl (c :: ZProof2Assumption z) (c :: ZProof2ConclusionOpt z).
Proof.
  intros c z Hentails modl Heval.
  simpl in *.
  (* Heval : EvalListZClause modl (c :: ZProof2Assumption z) *)
  (* So we know: evalZClause modl c = true and EvalListZClause modl (ZProof2Assumption z) *)
  apply andb_true_iff in Heval as [Hc Hass].

  (* Apply Hentails to get EvalListZClause modl (ZProof2ConclusionOpt z) *)
  specialize (Hentails modl Hass).

  (* Combine evalZClause modl c with Hentails *)
  apply andb_true_iff.
  split; assumption.
Qed.

Lemma ZProofCheck_Cons_Case :
  forall (l : ZProofItem) (p : ZProof),
  ZProofCheck (l :: p) = 
    andb (ZProofCheckLastStep (ZProof2ConclusionOpt p) l) (ZProofCheck p).
Proof.
intros.
reflexivity.
Qed.

Lemma contradiction_from_conflict : forall a : bool,
  a = true -> a = false -> False.
Proof.
  intros a Htrue Hfalse.
  rewrite Htrue in Hfalse.
  discriminate Hfalse.
Qed.

Lemma andb_false_elim :
  forall a b : bool,
    a && b = false ->
    a = false \/ b = false.
Proof.
  intros a b H.
  destruct a, b; simpl in H; try discriminate; auto.
Qed.

Lemma andb_false_split :
  forall a b : bool,
    a && b = false ->
    a = false \/ b = false.
Proof.
  intros a b H.
  apply andb_false_elim; assumption.
Qed.

Lemma ZProofCheck_rupZ3proof_head :
  forall (l : ZClause) (p' : list ZProofItem),
    ZProofCheckLastStep (ZProof2ConclusionOpt p') (rupZ3proof l) = true ->
    ZProofCheck p' = true ->
    RUP_Checker (ZProof2RupConclusions p') (zCl2RClause l) = true.
Proof.
  intros l p' pt H.
  destruct (ZProofCheck (rupZ3proof l :: p')) eqn:Hcheck.
  - (* Case: ZProofCheck = true *)
    rewrite ZProofCheck_Cons_Case in Hcheck.

    (* Now we can apply andb_prop *)
    apply andb_prop in Hcheck as [Hstep _].
    unfold ZProofCheckLastStep in Hstep.
    exact Hstep.
  - (* Case: ZProofCheck = false *)
    simpl in *.

    apply contradiction_from_conflict in H.
    contradiction.

    apply andb_false_split in Hcheck.
    destruct Hcheck as [HcL | HcR].
    + congruence.
    + assumption.
Qed.

Lemma Zfor2Lit_z3var :
  forall v,
    Zfor2Lit (z3var v) = pos (pos_z3var v).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_and :
  forall l,
    Zfor2Lit (and l) = pos (pos_and l).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_or :
  forall l,
    Zfor2Lit (or l) = pos (pos_or l).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_imply :
  forall a b,
    Zfor2Lit (imply a b) = pos (pos_imply a b).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_not_z3var :
  forall v,
    Zfor2Lit (not (z3var v)) = neg (pos_z3var v).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_not_and :
  forall l,
    Zfor2Lit (not (and l)) = neg (pos_and l).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_not_or :
  forall l,
    Zfor2Lit (not (or l)) = neg (pos_or l).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_not_imply :
  forall a b,
    Zfor2Lit (not (imply a b)) = neg (pos_imply a b).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma Zfor2Lit_double_negation :
  forall y,
    Zfor2Lit (not (not y)) = Zfor2Lit y.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma modelNot :
  forall (m : Model) (l : Literal),
  models_literal m (negate l) = negb (models_literal m l).
Proof.
  intros.
  destruct l.
  simpl. reflexivity.
  simpl. rewrite doubleNegBool. reflexivity.
Qed. 

Lemma models_not_rewrite :
  forall (m : Model) (f : Z3_Formula),
  models_literal m (Zfor2Lit (not f)) =
  negb (models_literal m (Zfor2Lit f)).
Proof.
  intros.
  induction f.
  - rewrite Zfor2Lit_not_z3var.
    simpl. reflexivity.
  - rewrite Zfor2Lit_not_and.
    simpl. reflexivity.
  - rewrite Zfor2Lit_not_or.
    simpl. reflexivity.
  - rewrite Zfor2Lit_not_imply.
    simpl. reflexivity.
  - rewrite Zfor2Lit_double_negation.
    rewrite IHf.
    rewrite doubleNegBool.
    reflexivity.
Qed.

Lemma Zfor2Lit_eval_equiv :
  forall (modl : ZModel) (f : Z3_Formula),
    models_literal (zModel2Rmodel modl) (Zfor2Lit f) = evalZFor modl f.
Proof.
  intros modl.
  induction f.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. reflexivity.
  +
    rewrite models_not_rewrite.
    simpl.
    congruence.
Qed.

Lemma rClauseZModel_equiv :
  forall (modl : ZModel) (c : ZClause),
    evalZClause modl c = models_clause (zModel2Rmodel modl) (zCl2RClause c).
Proof.
  intros modl c.
  induction c as [| f rest IH].
  - simpl. reflexivity.
  - simpl.
    (* Unfold evalZClause *)
    unfold evalZClause.
    simpl.

    (* Use IH: evalZClause modl rest = models_clause (zModel2Rmodel modl) (zCl2RClause rest) *)
    rewrite <- IH.

    (* Use Zfor2Lit_eval_equiv: models_literal (zModel2Rmodel modl) (Zfor2Lit f) = evalZFor modl f *)
    rewrite <- Zfor2Lit_eval_equiv.

    reflexivity.
Qed.

Lemma rListClZModel_equiv :
  forall (modl : ZModel) (cl : list ZClause),
    evalListZClause modl cl = models_formula (zModel2Rmodel modl) (zListCl2RListCl cl).
Proof.
  induction cl as [| c cs IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    rewrite rClauseZModel_equiv.
    reflexivity.
Qed.

Lemma rListClZModel_to_EvalRFor :
  forall (modl : ZModel) (cl : list ZClause),
    EvalListZClause modl cl ->
    Models_formula (zModel2Rmodel modl) (zListCl2RListCl cl).
Proof.
  intros modl cl H.

  unfold Models_formula.
  (* Use definitional equality if needed *)
  rewrite <- (rListClZModel_equiv modl cl).
 
  unfold EvalListZClause in H.
  unfold atom in H.
  unfold IsTrue.
  rewrite H.
  auto.
Qed.

Lemma rClauseZModel_forward :
  forall (modl : ZModel) (c : ZClause),
    EvalZClause modl c ->
    Models_clause (zModel2Rmodel modl) (zCl2RClause c).
Proof.
  intros modl c H.
  unfold EvalZClause, Models_clause.
  rewrite <- rClauseZModel_equiv.
  unfold EvalZClause in H.
  unfold IsTrue.
  rewrite H.
  auto.
Qed.

Lemma IsTrue_atom :
  forall a : bool, IsTrue a -> atom a.
Proof.
  intros a H.
  unfold atom.
  destruct a.
  - reflexivity.
  - contradiction.
Qed.

Lemma rClauseZModel_backward :
  forall (modl : ZModel) (c : ZClause),
    Models_clause (zModel2Rmodel modl) (zCl2RClause c) ->
    EvalZClause modl c.
Proof.
  intros modl c H.
  unfold EvalZClause, Models_clause.
  rewrite rClauseZModel_equiv.
  unfold Models_clause in H.
  apply IsTrue_atom.
  unfold IsTrue in *.
  assumption.
Qed.

Lemma entailsRCl2ZCl :
  forall (ass : list ZClause) (c : ZClause),
    entails (zListCl2RListCl ass) (zCl2RClause c) ->
    EntailsZCl ass c.
Proof.
  intros ass c ent modl Hass.
  (* Convert ZModel to RModel *)
  set (rmod := zModel2Rmodel modl).

  (* Use helper to lift evalListZClause to EvalRFor *)
  pose proof (rListClZModel_to_EvalRFor modl ass Hass) as p'.

  (* Apply entailment in R world *)
  specialize (ent rmod p').

  (* Convert RClause evaluation back to ZClause *)
  apply rClauseZModel_backward with (modl := modl) (c := c).
  exact ent.
Qed.

Lemma zListCl2RListCl_equiv :
  forall (zcs : list ZClause),
    zListCl2RListCl zcs = map zCl2RClause zcs.
Proof.
  induction zcs as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma entailsZCl_addInference' :
  forall (ass cl : list ZClause) (c : ZClause),
    EntailsListZCl ass cl ->
    EntailsZCl cl c ->
    EntailsZCl ass c.
Proof.
  intros ass cl c H_ascl H_clc modl H_eval_as.
  (* Use H_ascl to get EvalListZClause modl cl *)
  specialize (H_ascl modl H_eval_as).
  (* Apply H_clc to that *)
  apply H_clc.
  exact H_ascl.
Qed.

Lemma if_true_then_eq_true :
  forall x : bool, (if x then True else False) -> x = true.
Proof.
  intros x H.
  destruct x.
  - reflexivity.
  - simpl in H. contradiction.
Qed.

Lemma and_true_implies_each_true : forall a b : bool,
  (a && b = true) -> (a = true /\ b = true).
Proof.
  intros a b H.
  apply andb_true_iff in H.
  assumption.
Qed.

Definition rModel2ZModel (modl : Model) : ZModel :=
  fun v => modl (pos_z3var v).

Lemma Models_formula_cons :
  forall (m : Model) (c : Clause) (f : Formula),
    Models_formula m (c :: f) ->
    Models_clause m c /\ Models_formula m f.
Proof.
  intros m c f H.
  unfold Models_formula in H.
  simpl in H.
  unfold IsTrue in H.
  apply if_true_then_eq_true in H.
  apply andb_true_iff in H.
  destruct H as [Hc Hf].
  split.
  - unfold Models_clause, IsTrue. rewrite Hc. auto.
  - unfold Models_formula, IsTrue. rewrite Hf. auto.
Qed.

Lemma model_to_zmodel :
  forall m : Model, exists zm : ZModel, zm = rModel2ZModel m.
Proof.
  intros m.
  exists (rModel2ZModel m).
  reflexivity.
Qed.

Lemma EntailsGeneral :
  forall (al cl : list ZClause) (c : ZClause),
    EntailsListZCl al cl ->
    entails (zListCl2RListCl cl) (zCl2RClause c) ->
    EntailsZCl al c.
Proof.
intros.
apply entailsRCl2ZCl in H0.
apply entailsZCl_addInference' with al cl c in H.
assumption.
assumption.
Qed.

Lemma EntailsListZCl_RUP_step :
  forall (l : ZClause) (p' : ZProof),
    IsTrue (ZProofCheck (rupZ3proof l :: p')) ->
    EntailsListZCl (ZProof2Assumption p')
                   (ZProof2ConclusionOpt p') ->
    EntailsListZCl (ZProof2Assumption (rupZ3proof l :: p'))
                   (ZProof2ConclusionOpt (rupZ3proof l :: p')).
Proof.
  intros l p' Hcheck IH.

  apply entailsAddEntails.
  +
    simpl.

    unfold IsTrue in Hcheck.
    rewrite ZProofCheck_Cons_Case in Hcheck.
    apply if_true_then_eq_true in Hcheck.
    apply and_true_implies_each_true in Hcheck.
    destruct Hcheck as [H1 H2].

    apply ZProofCheck_rupZ3proof_head in H1.
    apply RUP_Checker_correct in H1.

    apply entailsRCl2ZCl in H1.

    apply entailsZCl_addInference' with (ZProof2ConclusionOpt p').
    assumption.
    assumption.
    assumption.
  +
    apply IH.
Qed.

Lemma tseitin_index_bound :
  forall (l : listZ3_Formula) (n : nat) (p' : ZProof),
    IsTrue ((n <? length_listZ3 l) && ZProofCheck p') ->
    n < length_listZ3 l.
Proof.
  intros l n p' Hcheck.
  unfold IsTrue in Hcheck.

  destruct ((n <? length_listZ3 l) && ZProofCheck p') eqn:Hbool.
  - (* Case: true *)
    apply andb_prop in Hbool as [Hlt _].
    apply Nat.ltb_lt. exact Hlt.

  - (* Case: false *)
    (* Contradiction: Hcheck says this branch is unreachable *)
    exfalso. exact Hcheck.
Qed.

Fixpoint removeZFormula (f : Z3_Formula) (c : ZClause) : ZClause :=
  match c with
  | lnil => lnil
  | lcons h t =>
      if Z3_Formula_eq_dec h f then removeZFormula f t
      else lcons h (removeZFormula f t)
end.

Fixpoint removeZFormulas (fs : listZ3_Formula) (c : ZClause) : ZClause :=
  match fs with
  | lnil => c
  | lcons f rest => removeZFormulas rest (removeZFormula f c)
  end.

Lemma evalZClause_cons :
  forall m a b,
    evalZClause m (lcons a b) = evalZFor m a || evalZClause m b.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma negb_true_iff_false : forall a : bool, negb a = true -> a = false.
Proof.
  intros a H.
  destruct a; simpl in H; try discriminate; reflexivity.
Qed.

(*
m models ls
and not m models a
m models ls without a
*)
Lemma oppositeZModel :
  forall (m : ZModel) (ls: listZ3_Formula) (a: Z3_Formula),
  evalZClause m ls = true ->
  negb (evalZFor m a) = true ->
  evalZClause m (removeZFormula a ls) = true.
Proof.
  intros m ls a Hclause Hneg.
  induction ls as [| f rest IH].
  - simpl in *. assumption.
  - simpl in *.
    destruct (Z3_Formula_eq_dec f a) eqn:Heq.
    + (* Case: f = a, so we remove it *)
      apply IH.
      * (* Need to show evalZClause m rest = true *)
        unfold evalZClause in Hclause.
        simpl in Hclause.

        rewrite e in Hclause.
        apply negb_true_iff_false in Hneg.
        rewrite Hneg in Hclause.
        simpl in Hclause.
        assumption.
    + (* Case: f ≠ a, so we keep it *)
      unfold evalZClause in *.
      simpl in *.
      (* evalZClause m (f :: rest) = true means evalZFor m f || evalZClause m rest = true *)
      destruct (evalZFor m f) eqn:Ef.
      * (* evalZFor m f = true *)
        simpl. reflexivity.
      * (* evalZFor m f = false *)
        simpl in Hclause.
        apply IH.
        (* evalZClause m rest = true *)
           exact Hclause.
Qed.

Lemma oppositeZModelNegFor :
  forall (m : ZModel) (ls : listZ3_Formula) (a : Z3_Formula),
    evalZClause m ls = true ->
    evalZFor m (negFor a) = true ->
    evalZClause m (removeZFormula a ls) = true.
Proof.
  intros m ls a Hclause Hneg.
  rewrite negForCorrect in Hneg.
  apply oppositeZModel; assumption.
Qed.

Lemma in_listZ3b_cons :
  forall f h t,
    in_listZ3b f (lcons h t) = true ->
    f = h \/ in_listZ3b f t = true.
Proof.
  intros f h t H.
  simpl in H.
  destruct (z3_formula_eq f h) eqn:Heq.
  - (* Case: f = h *)
    apply z3_formula_eq_eq in Heq. (* You need this spec lemma *)
    left. exact Heq.
  - (* Case: f ≠ h *)
    right. exact H.
Qed.

Lemma in_listZ3b_cons_case :
  forall f h t,
    z3_formula_eq f h || in_listZ3b f t = true ->
    f <> h ->
    in_listZ3b f t = true.
Proof.
  intros f h t H Hneq.
  assert (z3_formula_eq f h = false).
  {
    destruct (z3_formula_eq f h) eqn:Heq.
    - apply z3_formula_eq_eq in Heq. (* Assuming you have a spec lemma *)
      contradiction.
    - reflexivity.
  }
  rewrite H0 in H.
  simpl in H.
  apply H.
Qed.

Fixpoint lengthZ3 (l : listZ3_Formula) : nat :=
  match l with
  | lnil => 0
  | lcons _ t => S (lengthZ3 t)
  end.

Lemma removeZFormula_length_le :
  forall f ls,
    lengthZ3 (removeZFormula f ls) <= lengthZ3 ls.
Proof.
  intros f ls.
  induction ls as [| h t IH].
  - simpl. apply le_n.
  - simpl.
    destruct (Z3_Formula_eq_dec h f).
    + apply le_S. apply IH.
    + simpl. apply le_n_S. apply IH.
Qed.

Lemma removeZFormula_length_lt :
  forall f ls,
    in_listZ3b f ls = true ->
    lengthZ3 (removeZFormula f ls) < lengthZ3 ls.
Proof.
  intros f ls.
  induction ls as [| h t IH].
  - simpl. intros H. discriminate.
  - simpl. intros Hin.
    simpl in Hin.
    destruct (Z3_Formula_eq_dec h f) as [Heq | Hneq].
    + (* Case: h = f, so we remove it *)
      apply Nat.lt_succ_r.
      apply removeZFormula_length_le.
    + (* Case: h ≠ f, so we keep h *)
      simpl.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin_eq | Hin_in].
      * (* z3_formula_eq f h = true implies f = h, contradiction *)
        apply z3_formula_eq_eq in Hin_eq.
        symmetry in Hin_eq.
        contradiction.
      * (* f is in t *)
        specialize (IH Hin_in).
        simpl.
        apply Nat.lt_succ_r.
        exact IH.
Qed.

Lemma false_implies_negb_true :
  forall a : bool, a = false -> negb a = true.
Proof.
intros a H.
rewrite H.
simpl.
reflexivity.
Qed.

Lemma negatedModelF :
  forall (m : ZModel) (f : Z3_Formula),
  negb (evalZFor m f) = true <-> evalZFor m (negFor f) = true.
Proof.
  intros m f.
  split; intros H.
  - (* -> direction *)
    destruct f; simpl in *; try assumption.
    + (* f = Not x *)
      rewrite doubleNegBool in H. assumption.
  - (* <- direction *)
    destruct f; simpl in *; try assumption.
    + (* f = Not x *)
      unfold negFor in H. 
      rewrite doubleNegBool. assumption.
Qed.

Lemma oppositeZModelList :
  forall (m : ZModel) (ls fs : listZ3_Formula),
    evalZClause m ls = true ->
    evalListZClause m (negSingletons fs) = true ->
    evalZClause m (removeZFormulas fs ls) = true.
Proof.
  intros m ls fs Hls Hneg.
  generalize dependent ls. (* This moves ls out of the context *)
  induction fs as [| f rest IH].
  - (* Base case: fs = lnil *)
    intros ls Hls.
    simpl. exact Hls.

  - (* Inductive case: fs = lcons f rest *)
    intros ls Hls.
    simpl in Hneg.
    apply andb_prop in Hneg as [Hnotf Hrest].

    (* Step 1: evalZFor m (not f) = true *)
    rewrite evalZClause_cons in Hnotf.

    simpl in Hnotf.
    rewrite Bool.orb_false_r in Hnotf.

    apply negatedModelF in Hnotf.

    (* Step 2: evalZFor m f = false *)
    apply negb_true_iff_false in Hnotf.

    (* Step 3: Remove f from ls *)
    assert (Hremove : evalZClause m (removeZFormula f ls) = true).
    {
      apply oppositeZModel.
      assumption.
      apply false_implies_negb_true.
      assumption.
    }

    (* Step 4: Apply IH to rest and reduced clause *)
    apply IH; assumption.
Qed.

Lemma and_true_eq_true_implies_eq_true :
  forall A : bool,
    A && true = true ->
    A = true.
Proof.
  intros A H.
  destruct A; simpl in *; auto; discriminate.
Qed.

Lemma oppositeZModelListEntails :
  forall (a : list (ZClause)) (ls fs : listZ3_Formula),
    EntailsListZCl a [ls] ->
    EntailsListZCl a (negSingletons fs) ->
    EntailsListZCl a [(removeZFormulas fs ls)].
Proof.
  intros m ls fs Hls Hneg.

  unfold EntailsListZCl.
  intros.
  unfold EvalListZClause.
  unfold atom.
  simpl.
  apply andb_true_intro.
  split.
  + apply oppositeZModelList.
    - 
    unfold EntailsListZCl in Hls.
    unfold EvalListZClause in Hls.
    unfold atom in Hls.
    simpl in Hls.
    specialize (Hls modl).
    specialize (Hls H).
    apply and_true_eq_true_implies_eq_true in Hls.
    assumption.

    -
    unfold EntailsListZCl in Hneg.
    unfold EvalListZClause in Hneg.
    unfold atom in Hneg.
    apply Hneg.
    assumption.

  + 
    reflexivity.
Qed.

Fixpoint listZ3_to_list (l : listZ3_Formula) : list Z3_Formula :=
  match l with
  | lnil => []
  | lcons x xs => x :: listZ3_to_list xs
  end.

Fixpoint list_to_listZ3 (l : list Z3_Formula) : listZ3_Formula :=
  match l with
  | [] => lnil
  | x :: xs => lcons x (list_to_listZ3 xs)
  end.

Lemma listZ3_to_list_inverse :
  forall (l : list Z3_Formula),
    listZ3_to_list (list_to_listZ3 l) = l.
Proof.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma list_to_listZ3_inverse :
  forall (l' : listZ3_Formula),
    list_to_listZ3 (listZ3_to_list l') = l'.
Proof.
  induction l' as [| x xs IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Fixpoint list_setminus (a b : list Z3_Formula) : list Z3_Formula :=
  match a with
  | [] => []
  | x :: xs =>
      if in_listZ3b x (list_to_listZ3 b) then
        list_setminus xs b
      else
        x :: list_setminus xs b
  end.

Lemma list_to_listZ3_setminus_preserved :
  forall a b : list Z3_Formula,
    list_to_listZ3 (list_setminus a b) =
    setminus (list_to_listZ3 a) (list_to_listZ3 b).
Proof.
  induction a as [| x xs IH]; intros b.
  - simpl. reflexivity.
  - simpl. remember (in_listZ3b x (list_to_listZ3 b)) as inb.
    destruct inb.
    + simpl. apply IH.
    + simpl. f_equal. apply IH.
Qed.

Lemma in_listZ3b_preserved :
  forall x b,
    in_listZ3b x b = in_listZ3b x (list_to_listZ3 (listZ3_to_list b)).
Proof.
  intros x b.
  induction b as [| y ys IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma listZ3_to_list_setminus_preserved :
  forall a b : listZ3_Formula,
    listZ3_to_list (setminus a b) =
    list_setminus (listZ3_to_list a) (listZ3_to_list b).
Proof.
  induction a as [| x xs IH]; intros b.
  - simpl. reflexivity.
  - simpl.
    rewrite in_listZ3b_preserved.
    destruct (in_listZ3b x (list_to_listZ3 (listZ3_to_list b))) eqn:Hin.
    + apply IH.
    + simpl. f_equal. apply IH.
Qed.

Fixpoint list_subset (l1 l2 : list Z3_Formula) : bool :=
  match l1 with
  | [] => true
  | x :: xs => in_listZ3b x (list_to_listZ3 l2) && list_subset xs l2
  end.

Lemma listZ3_to_list_normalize :
  forall l : listZ3_Formula,
    listZ3_to_list (list_to_listZ3 (listZ3_to_list l)) = listZ3_to_list l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma list_to_listZ3_normalize :
  forall l : list Z3_Formula,
    list_to_listZ3 (listZ3_to_list (list_to_listZ3 l)) = list_to_listZ3 l.
Proof.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Lemma listZ3_subset_to_list_preserves_subset :
  forall c l : listZ3_Formula,
    listZ3_subset c l = true ->
    listZ3_subset (list_to_listZ3 (listZ3_to_list c)) (list_to_listZ3 (listZ3_to_list l)) = true.
Proof.
  intros c l H.
  induction c as [| x xs IH].
  - simpl. reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hin Hsub].
    simpl. rewrite <- in_listZ3b_preserved. rewrite Hin.
    apply IH in Hsub. rewrite Hsub. reflexivity.
Qed.

Lemma listZ3_subset_from_list_preserves_subset :
  forall c l : listZ3_Formula,
    listZ3_subset (list_to_listZ3 (listZ3_to_list c)) (list_to_listZ3 (listZ3_to_list l)) = true ->
    listZ3_subset c l = true.
Proof.
  intros c l H.
  assert (list_to_listZ3 (listZ3_to_list c) = c) by apply list_to_listZ3_inverse.
  assert (list_to_listZ3 (listZ3_to_list l) = l) by apply list_to_listZ3_inverse.
  rewrite <- H0, <- H1. exact H.
Qed.

Definition listZ3_equiv (l1 l2 : listZ3_Formula) : Prop :=
  listZ3_subset l1 l2 = true /\ listZ3_subset l2 l1 = true.

Lemma z3_formula_eq_refl :
  forall f : Z3_Formula, z3_formula_eq f f = true.
Proof.
  Scheme Z3_Formula_mut := Induction for Z3_Formula Sort Prop
  with listZ3_Formula_mut := Induction for listZ3_Formula Sort Prop.

  intros f.
  induction f using Z3_Formula_mut with
    (P0 := fun l => list_z3_formula_eq l l = true).
  - (* z3var *)
    simpl. apply String.eqb_refl.
  - (* and *)
    simpl. apply IHf.
  - (* or *)
    simpl. apply IHf.
  - (* imply *)
    simpl. rewrite IHf1, IHf2. reflexivity.
  - (* not *)
    simpl. apply IHf.

  - simpl. reflexivity.
  - simpl. rewrite IHf. rewrite IHf0. auto. 
Qed.

Lemma evalZClause_cons_remove :
  forall m h f t,
    evalZClause m (lcons h (removeZFormula f t)) =
    evalZFor m h || evalZClause m (removeZFormula f t).
Proof.
  intros. reflexivity.
Qed.

Lemma orb_eq_right :
  forall a b c : bool,
    b = c ->
    a || b = a || c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma evalZClause_remove :
  forall (m : ZModel) (f : Z3_Formula) (c : listZ3_Formula),
    in_listZ3b f c = false ->
    evalZClause m c = evalZClause m (removeZFormula f c).
Proof.
  intros m f c.
  induction c as [| h t IH]; intros H.
  - simpl. reflexivity.
  - simpl in H.
    apply Bool.orb_false_iff in H as [Hfh Hft].
    simpl.
    destruct (Z3_Formula_eq_dec h f) as [Heq | Hneq].
    + (* h = f, contradiction with Hfh *)
      rewrite Heq in Hfh.
      unfold z3_formula_eq in Hfh.
      (* Assuming z3_formula_eq f f = true *)
      rewrite z3_formula_eq_refl in Hfh.
      discriminate.
    + (* h ≠ f *)
      rewrite evalZClause_cons_remove.
      rewrite evalZClause_cons.
      apply orb_eq_right.
      rewrite IH; auto.
Qed.

Fixpoint toZClause (l : list Z3_Formula) : ZClause :=
  match l with
  | [] => lnil
  | h :: t => lcons h (toZClause t)
end.

Lemma orb_false_r_true :
  forall b : bool,
    b || false = true -> b = true.
Proof.
  intros b H.
  destruct b.
  - reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma evalZClause_remove_negated :
  forall (m : ZModel) (c : ZClause) (l : Z3_Formula),
    EvalZClause m c ->
    EvalZClause m (toZClause [l]) ->
    EvalZClause m (removeZFormula (not l) c).
Proof.
  intros m c l Hc Hl.
  unfold EvalZClause in *.
  unfold atom in *.
  unfold evalZClause in *.

  (* evalZClause m [l] = true means evalZFor m l = true *)
  simpl in Hl.
  assert (Hnotl : evalZFor m (not l) = false).
  {
    simpl. 
    apply orb_false_r_true in Hl.
    rewrite Hl. reflexivity.
  }

  (* Now we want to show that removing a false formula from a disjunction keeps it true *)
  (* This can be done by induction on c *)
  induction c as [| f rest IH].
  - simpl. simpl in Hc. assumption.
  - simpl in Hc. simpl.
    destruct (Z3_Formula_eq_dec f (not l)).
    + (* f = not l, so evalZFor f = false *)
      rewrite <- e in Hnotl.
      simpl in Hc.
      apply orb_true_iff in Hc.
      destruct Hc as [Hf | Hrest].
      * rewrite Hnotl in Hf. discriminate.
      * apply IH in Hrest. assumption.
    + (* f ≠ not l *)
      simpl.
      apply orb_true_iff in Hc.
      destruct Hc as [Hf | Hrest].
      * apply orb_true_iff. left. assumption.
      * apply IH in Hrest. apply orb_true_iff. right. assumption.
Qed.

Lemma ZTaut_implies_eval :
  forall (c : ZClause) (m : ZModel),
    ZTaut c ->
    EvalZClause m c.
Proof.
  intros c m H.
  unfold EvalZClause.
  unfold ZTaut in H.
  apply H.
Qed.

Lemma in_listZ3List_correct :
  forall x l,
    in_listZ3List x l = true -> In x l.
Proof.
  intros x l.
  induction l as [| y ys IH].
  - simpl. intros H. discriminate.
  - simpl. intros H.
    apply orb_true_iff in H.
    destruct H as [Heq | Hin].
    + apply list_z3_formula_eq_eq in Heq. subst. left. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma listZ3List_subset_inclusion :
  forall (l1 l2 : list ZClause),
    listZ3List_subset l1 l2 = true ->
    forall c, In c l1 -> In c l2.
Proof.
  intros l1 l2 Hsubset.
  induction l1 as [| x xs IH].
  - intros c H. inversion H. (* Nothing in empty list *)
  - simpl in Hsubset.
    apply andb_true_iff in Hsubset as [Hinx Hrest].
    intros c H.
    simpl in H.
    destruct H as [Heq | Hin].
    + subst. apply in_listZ3List_correct. assumption.
    + apply IH. assumption. assumption.
Qed.

Lemma EvalListZClause_cons :
  forall (m : ZModel) (c : ZClause) (cs : list ZClause),
    EvalListZClause m (c :: cs) <-> EvalZClause m c /\ EvalListZClause m cs.
Proof.
  intros m c cs.
  unfold EvalListZClause, atom, evalListZClause.
  simpl.
  split.
  - (* -> direction *)
    intros H.
    apply andb_true_iff in H as [Hc Hcs].
    split; assumption.
  - (* <- direction *)
    intros [Hc Hcs].
    apply andb_true_iff.
    split; assumption.
Qed.

Lemma EvalListZClause_in :
  forall (m : ZModel) (l : list ZClause) (c : ZClause),
    EvalListZClause m l ->
    In c l ->
    EvalZClause m c.
Proof.
  intros m l c Heval Hin.
  unfold EvalListZClause, atom in Heval.
  induction l as [| x xs IH].
  - inversion Hin. (* contradiction: nothing is in [] *)
  - simpl in Heval.
    simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst. (* c = x *)
      apply andb_true_iff in Heval as [Hx _].
      exact Hx.
    + apply andb_true_iff in Heval as [_ Hxs].
      apply IH; assumption.
Qed.

Lemma EvalListZClause_subset :
  forall (m : ZModel) (l1 l2 : list ZClause),
    listZ3List_subset l1 l2 = true ->
    EvalListZClause m l2 ->
    EvalListZClause m l1.
Proof.
  intros m l1 l2 Hsub Heval.
  unfold EvalListZClause, atom, evalListZClause in *.
  induction l1 as [| c cs IH].
  - reflexivity.
  - simpl in Hsub.
    apply andb_true_iff in Hsub as [Hin Hrest].
    apply in_listZ3List_correct in Hin.
    apply andb_true_iff.
    split.
    + apply EvalListZClause_in with (l := l2); assumption.
    + apply IH; assumption.
Qed.

Lemma EvalListZClause_singleton_clause :
  forall (m : ZModel) (l : Z3_Formula),
    EvalListZClause m [lcons l lnil] ->
    EvalZClause m (toZClause [l]).
Proof.
  intros m l H.
  unfold EvalListZClause, atom, evalListZClause in H.
  simpl in H.
  (* evalListZClause m [lcons l lnil] = evalZClause m (lcons l lnil) && true *)
  apply andb_true_iff in H as [Hclause _].
  unfold EvalZClause, atom.
  exact Hclause.
Qed.

Lemma EvalZClause_from_singleton_subset :
  forall (m : ZModel) (l : Z3_Formula) (l2 : list ZClause),
    listZ3List_subset [lcons l lnil] l2 = true ->
    EvalListZClause m l2 ->
    EvalZClause m (toZClause [l]).
Proof.
  intros m l l2 Hsub Heval.
  (* Use EvalListZClause_subset to get EvalListZClause m [lcons l lnil] *)
  apply EvalListZClause_subset with m [lcons l lnil] l2 in Hsub. try assumption.
  (* Use EvalListZClause_singleton_clause to get EvalZClause m (toZClause [l]) *)
  apply EvalListZClause_singleton_clause in Hsub.
  exact Hsub. assumption.
Qed.

Lemma EvalZClause_from_singleton_subset' :
  forall (m : ZModel) (l : listZ3_Formula) (l2 : list ZClause),
    listZ3List_subset [l] l2 = true ->
    EvalListZClause m l2 ->
    EvalZClause m l.
Proof.
  intros m l l2 Hsub Heval.
  (* Use EvalListZClause_subset to get EvalListZClause m [lcons l lnil] *)
  apply EvalListZClause_subset with m [l] l2 in Hsub. 
  unfold EvalListZClause in Hsub. 
  simpl in Hsub.
  unfold atom in Hsub.
  apply andb_true_iff in Hsub as [Hclause _].
  assumption.
  assumption.
Qed.

Lemma tseitin_check :
  forall l a,
    IsTrue (ZProofCheckTseitin l) ->
    EntailsZCl a (TseitinProofItem2ConclusionOpt l).
Proof.
intros.
destruct l.
  +
    (* Not *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinNotTaut.

  + (* Imp Elim *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinImpElimTaut.

  + (* Imp Intro 1 *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinImpIntro1Taut.

  + (* Imp Intro 2 *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinImpIntro2Taut.

  + (* Imp Intro 3 *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinImpIntro3Taut.

  + (* And Intro *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinAndIntroTaut.

  + (* And Elim *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinAndElimTaut.

    simpl in *.
    unfold IsTrue in H.
    destruct (n <? length_listZ3 l) eqn:Hcmp.
    - (* Case: n <? length_listZ3 l = true *)
      apply Nat.ltb_lt in Hcmp.
      exact Hcmp.

    - (* Case: n <? length_listZ3 l = false *)
      contradiction.

  + (* Or Intro *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinOrIntroTaut.

    simpl in *.
    unfold IsTrue in H.
    destruct (n <? length_listZ3 l) eqn:Hcmp.
    - (* Case: n <? length_listZ3 l = true *)
      apply Nat.ltb_lt in Hcmp.
      exact Hcmp.

    - (* Case: n <? length_listZ3 l = false *)
      contradiction.

  + (* Or Elim *)
    simpl.
    unfold EntailsZCl.
    intros.
    apply tseitinOrElimTaut.
Qed.

Lemma tseitin_entails :
  forall l p',
    IsTrue (ZProofCheck (tseitinStep l :: p')) ->
    (IsTrue (ZProofCheck p') ->
    EntailsListZCl (ZProof2Assumption p') (ZProof2ConclusionOpt p')) ->
    EntailsListZCl (ZProof2Assumption (tseitinStep l :: p'))
                   (ZProof2ConclusionOpt (tseitinStep l :: p')).
Proof.
intros.
destruct l.
  + (* Not *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinNotTaut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Imp Elim *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinImpElimTaut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Imp Intro 1 *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinImpIntro1Taut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Imp Intro 2 *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinImpIntro2Taut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Imp Intro 3 *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinImpIntro3Taut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* And Intro *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinAndIntroTaut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* And Elim *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinAndElimTaut.
      apply tseitin_index_bound with p'.
      exact H.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Or Intro *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinOrIntroTaut.
      apply tseitin_index_bound with p'.
      exact H.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.

  + (* Or Elim *)
    (* Apply entailsAddTaut *)
    apply entailsAddTaut.
    * (* Prove ZTaut tseitinNot2For z *)
      apply tseitinOrElimTaut.
    * apply H0. 
      apply IsTrue_andb_split in H as [Hstep Hrec].
      assumption.
Qed.

Lemma orListBool_true_if_some_true :
  forall l : list bool,
    (exists b : bool, In b l /\ b = true) ->
    orListBool l = true.
Proof.
  intros l [b [Hin Hb]].
  induction l as [| x xs IH].
  - inversion Hin. (* contradiction: b ∈ [] *)
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst x. rewrite Hb. simpl. reflexivity.
    + simpl. destruct x.
      * simpl. reflexivity.
      * simpl. specialize (IH Hin'). assumption.
Qed.

Lemma orListBool_true_implies_some_true :
  forall l : list bool,
    orListBool l = true ->
    exists b : bool, In b l /\ b = true.
Proof.
  induction l as [| x xs IH].
  - simpl. intros H. discriminate H.
  - simpl. destruct x.
    + intros _. exists true. split; [left; reflexivity | reflexivity].
    + intros H. apply IH in H. destruct H as [b [Hin Hb]].
      exists b. split; [right; exact Hin | exact Hb].
Qed.

Lemma evalListZFor_in :
  forall modl f l,
    in_listZ3b f l = true ->
    In (evalZFor modl f) (evalListZFor modl l).
Proof.
  intros modl f l Hin.
  induction l as [| f' rest IH].
  - simpl in Hin. discriminate.
  - simpl in Hin. simpl.
    apply orb_true_iff in Hin.
    destruct Hin as [Heq | Hin'].
    + apply z3_formula_eq_eq in Heq. subst f'. left. reflexivity.
    + right. apply IH. exact Hin'.
Qed.

Lemma negb_or_false_eq_true_implies_false :
  forall b : bool, negb b || false = true -> b = false.
Proof.
  intros b H.
  simpl in H.
  destruct b.
  - simpl in H. discriminate.
  - reflexivity.
Qed.

Lemma negSingletons_entail_false :
  forall a l modl,
    EntailsListZCl a (negSingletons l) ->
    evalListZClause modl a = true ->
    forall f, in_listZ3b f l = true -> evalZFor modl f = false.
Proof.
  intros a l modl Hent Hmodl f Hin.
  unfold EntailsListZCl in Hent.
  specialize (Hent modl Hmodl).
  unfold EvalListZClause in Hent.
  unfold evalListZClause in Hent.

  (* We'll use induction on l to match negSingletons l *)
  induction l as [| f' rest IH].
  - simpl in Hin. discriminate.
  - simpl in Hin.
    apply Bool.orb_true_iff in Hin as [Heq | Hin'].
    + (* Case: f = f' *)
      apply z3_formula_eq_eq in Heq. subst f'.

      (* Now look at the first clause in negSingletons: [¬f] *)
      simpl in Hent.
      apply andb_prop in Hent as [Hhd _].
      unfold evalZClause in Hhd. simpl in Hhd.

      (* evalZClause modl [¬f] = evalZFor modl (¬f) = true ⇒ evalZFor modl f = false *)
      destruct (evalZFor modl (not f)) eqn:Heval.
      * apply negb_true_iff in Heval. exact Heval.
      *
apply orb_false_r_true in Hhd.

        apply negatedModelF in Hhd.
        apply negb_true_iff_false in Hhd. assumption.
(*
        apply negb_or_false_eq_true_implies_false in Hhd. assumption.
*)
    + (* Case: f ∈ rest *)
      simpl in Hent.
      apply andb_prop in Hent as [_ Htl].
      apply IH; assumption.
Qed.

Lemma orb_true_r : forall b : bool, b || true = true.
Proof.
  intros b. destruct b; simpl; reflexivity.
Qed.

Lemma evalZClause_true_some_formula_true :
  forall modl cl,
    evalZClause modl cl = true ->
    exists f, in_listZ3b f cl = true /\ evalZFor modl f = true.
Proof.
  intros modl cl H.
  unfold evalZClause in H.
  unfold evalListZFor in H.

  induction cl as [| f rest IH].
  - simpl in H. discriminate.
  - simpl in H.
    apply Bool.orb_true_iff in H as [Hf | Hrest].
    + exists f. split.
      * simpl. rewrite z3_formula_eq_refl. reflexivity.
      * exact Hf.
    + destruct IH as [f' [Hin Heval]]; auto.
      exists f'. split.
      * simpl. rewrite Hin. apply orb_true_r.
      * exact Heval.
Qed.

Lemma in_listZ3b_not_in_setminus :
  forall f l1 l2,
    in_listZ3b f l1 = true ->
    in_listZ3b f (setminus l1 l2) = false ->
    in_listZ3b f l2 = true.
Proof.
  intros f l1 l2 Hin1 Hnotin.
  induction l1 as [| f' rest IH].
  - simpl in Hin1. discriminate.
  - simpl in Hin1. simpl in Hnotin.
    apply Bool.orb_true_iff in Hin1 as [Heq | Hin_rest].
    + apply z3_formula_eq_eq in Heq. subst f'.
      destruct (in_listZ3b f l2) eqn:Hfc.
      * reflexivity.
      * simpl in Hnotin.
        rewrite z3_formula_eq_refl in Hnotin.
        simpl in Hnotin.
        discriminate.
    + destruct (in_listZ3b f' l2) eqn:a.
      * apply IH; assumption.
      * simpl in Hnotin.
        destruct (z3_formula_eq f f') eqn:Heq.
        -- simpl in Hnotin. discriminate.
        -- apply IH; assumption.
Qed.

Lemma in_listZ3b_cons_false :
  forall f f' l,
    in_listZ3b f (lcons f' l) = false ->
    in_listZ3b f l = false.
Proof.
  intros f f' l H.
  simpl in H.
  apply Bool.orb_false_iff in H as [_ Hrest].
  exact Hrest.
Qed.

Lemma in_listZ3b_lcons :
  forall f x xs,
    in_listZ3b f (lcons x xs) = true ->
    f = x \/ in_listZ3b f xs = true.
Proof.
  intros f x xs H.
  simpl in H.
  (* in_listZ3b f (lcons x xs) = Z3_Formula_eqb f x || in_listZ3b f xs *)
  apply orb_true_iff in H.
  destruct H as [Heq | Hin_tail].
  - apply z3_formula_eq_eq in Heq. left; assumption.
  - right; assumption.
Qed.

Lemma in_listZ3b_setminus_tail :
  forall f f0 rest c,
    in_listZ3b f0 c = true ->
    in_listZ3b f (setminus (lcons f0 rest) c) = false ->
    in_listZ3b f (setminus rest c) = false.
Proof.
  intros f f0 rest c Hf0_in_c Hsetminus.
  simpl in Hf0_in_c.
  simpl in Hsetminus.
  (* Since f0 ∈ c, setminus (f0 :: rest) c = setminus rest c *)
  rewrite Hf0_in_c in Hsetminus.
  (* So Hsetminus is exactly in_listZ3b f (setminus rest c) = false *)
  exact Hsetminus.
Qed.

Lemma evalZFor_true_in_listZ3b_implies_evalZClause_true :
  forall modl f c,
    in_listZ3b f c = true ->
    evalZFor modl f = true ->
    evalZClause modl c = true.
Proof.
  intros modl f c Hin Heval.
  unfold evalZClause.
  unfold evalListZFor.
  induction c as [| f' rest IH].
  - simpl in Hin. discriminate.
  - simpl in Hin. simpl.
    apply Bool.orb_true_iff.
    destruct (z3_formula_eq f f') eqn:Heq.
    + left. apply z3_formula_eq_eq in Heq. subst. exact Heval.
    + right. apply IH.
      simpl in Hin.
      assumption.
Qed.

Lemma eq_implies_in_listZ3b :
  forall f x xs,
    z3_formula_eq f x = true ->
    in_listZ3b f (lcons x xs) = true.
Proof.
  intros f x xs Heq.
  simpl.
  rewrite Heq.
  apply Bool.orb_true_l.
Qed.

Lemma and_true_implies_each_true_reverse : forall a b : bool,
  (a = true /\ b = true) -> (a && b = true).
Proof.
  intros a b H.
  apply andb_true_iff in H.
  assumption.
Qed.

Lemma evalZClause_true_if_member_true :
  forall modl f c,
    in_listZ3b f c = true ->
    evalZFor modl f = true ->
    evalZClause modl c = true.
Proof.
  intros modl f c H_in H_eval.
  unfold evalZClause.
  induction c as [| f' rest IH].
  - simpl in H_in. discriminate. (* in_listZ3b f [] = false *)
  - simpl in H_in.
    apply Bool.orb_true_iff in H_in.
    destruct H_in as [H_eq | H_in_rest].

    +
    pose proof (proj1 (z3_formula_eq_eq f f')) as Hfeq.
    apply z3_formula_eq_eq in H_eq.
    subst.
    simpl.
    rewrite H_eval.
    simpl.
    reflexivity.

    +
    simpl.
    apply orb_true_iff.
    right.
    apply IH.
    assumption.
Qed.

Lemma listZ3_subset_preserves_membership :
  forall f c' c,
    listZ3_subset c' c = true ->
    in_listZ3b f c' = true ->
    in_listZ3b f c = true.
Proof.
  intros f c' c Hsub Hin.
  induction c' as [| x xs IH].
  - simpl in Hin. discriminate.
  - simpl in Hsub, Hin.
    apply andb_true_iff in Hsub.
    destruct Hsub as [Hin_x Hsub_xs].
    simpl in Hin.
    apply orb_true_iff in Hin.
    destruct Hin as [Heq | Hin_rest].
    + (* Case: f = x *)
      (* z3_formula_eq f x = true *)
      (* So f = x, and x ∈ c by Hin_x *)
      apply z3_formula_eq_eq in Heq.
      subst.
      assumption.
    + (* Case: f ∈ xs *)
      apply IH; assumption.
Qed.

Lemma orListBool_true_implies_exists_formula :
  forall modl l,
    orListBool (evalListZFor modl l) = true ->
    exists f, in_listZ3b f l = true /\ evalZFor modl f = true.
Proof.
  intros modl l.
  induction l as [| f rest IH].
  - simpl. intros H. discriminate.
  - simpl. destruct (evalZFor modl f) eqn:Hf.
    + intros _. exists f. split.
      * rewrite z3_formula_eq_refl. simpl. reflexivity.
      * assumption.
    + simpl. intros H.
      apply IH in H.
      destruct H as [f' [Hin Heval]].
      exists f'. split.
      * rewrite Hin. rewrite Bool.orb_true_r. reflexivity.
      * assumption.
Qed.

Lemma in_full_not_in_c_implies_in_setminus :
  forall f full c,
    in_listZ3b f full = true ->
    in_listZ3b f c = false ->
    in_listZ3b f (setminus full c) = true.
Proof.
  intros f full c Hin_full Hin_c.
  induction full as [| x xs IH].
  - simpl in Hin_full. discriminate.
  - simpl in Hin_full.
    apply Bool.orb_true_iff in Hin_full.
    destruct Hin_full as [Hfx | Hin_xs].
    + (* Case: f = x *)
      pose proof (proj1 (z3_formula_eq_eq f x)) as Hfeq.
      apply Hfeq in Hfx. subst x.
      simpl.
      rewrite Hin_c.
      simpl. rewrite z3_formula_eq_refl. rewrite Bool.orb_true_l. reflexivity.
    + (* Case: f ∈ xs *)
      simpl.
      destruct (in_listZ3b x c) eqn:Hx_c.
      * apply IH; assumption.
      * simpl. apply Bool.orb_true_iff. right. apply IH; assumption.
Qed.

Lemma clause_split_entailment_named :
  forall modl full c,
    evalZClause modl full = true ->
    listZ3_subset c full = true ->
    (forall f, in_listZ3b f (setminus full c) = true -> 
      evalZFor modl f = false) ->
    evalZClause modl c = true.
Proof.
  intros modl full c Hfull Hsub Hminus.
  unfold evalZClause in *.

  (* From Hfull: orListBool (evalListZFor modl full) = true *)
  (* So there exists f ∈ full such that evalZFor modl f = true *)
  assert (exists f, in_listZ3b f full = true /\ evalZFor modl f = true).
  { apply orListBool_true_implies_exists_formula. assumption. } (* helper: orListBool_true_implies_exists_formula *)

  destruct H as [f [Hin_full Heval_f]].

  (* Case split: is f ∈ c or f ∈ setminus full c? *)
  assert (in_listZ3b f c = true).
  {
    destruct (in_listZ3b f c) eqn:Hinc.
    - reflexivity.
    - (* Then f ∈ setminus full c *)
      assert (in_listZ3b f (setminus full c) = true).
      { apply in_full_not_in_c_implies_in_setminus.
        assumption.
        assumption.
      } (* helper: in_full_not_in_c_implies_in_setminus *)
      specialize (Hminus f H).
      rewrite Heval_f in Hminus.
      discriminate. (* contradiction: f evaluates to true, but Hminus says false *)
  }

  (* Now apply evalZClause_true_if_member_true *)
  apply evalZClause_true_if_member_true with (f := f).
  - assumption.
  - assumption.
Qed.

Lemma SetMinusEntails :
  forall (a : list ZClause) (ls: TseitinStep) (c : listZ3_Formula),
    EntailsZCl a (TseitinProofItem2ConclusionOpt ls) ->
    EntailsListZCl a (negSingletons (setminus (TseitinProofItem2ConclusionOpt ls) c)) ->
    listZ3_subset c (TseitinProofItem2ConclusionOpt ls) = true ->
    EntailsZCl a c.
Proof.
  intros a ls c Hent_full Hent_neg_subset Hsubset.
  unfold EntailsZCl in *.
  intros modl Hmodl.

  set (full := TseitinProofItem2ConclusionOpt ls).

  (* From negSingletons entailment, get that all f ∈ (full \ c) are false *)
  assert (Hfalse : forall f, in_listZ3b f (setminus full c) = true -> evalZFor modl f = false).
  {
    apply negSingletons_entail_false with (a := a); auto.
  }

  (* From full clause entailment *)
  specialize (Hent_full modl Hmodl).

  (* Use helper lemma to conclude c must evaluate to true *)
  apply clause_split_entailment_named with full. auto. auto. auto.
Qed.

Lemma evalListZClause_includes :
  forall modl l c,
    in_listZ3List c l = true ->
    evalListZClause modl l = true ->
    evalZClause modl c = true.
Proof.
  intros modl l.
  induction l as [| d ds IH]; intros c Hin Heval.
  - simpl in Hin. discriminate.
  - simpl in Hin, Heval.
    apply orb_true_iff in Hin.
    apply andb_true_iff in Heval as [Hd Hds].
    destruct Hin as [Heq | Hin'].
    + (* Case: c = d *)
      apply list_z3_formula_eq_eq in Heq.
      subst. exact Hd.
    + (* Case: c ∈ ds *)
      apply IH; assumption.
Qed.

Lemma EntailsListZCl_subset :
  forall A B C,
    EntailsListZCl A B ->
    listZ3List_subset C B = true ->
    EntailsListZCl A C.
Proof.
  intros A B C Hentails Hsubset.
  unfold EntailsListZCl in *.
  intros modl Hassump.
  induction C as [| c cs IH].
  - simpl. constructor.
  - simpl in Hsubset.
    apply andb_true_iff in Hsubset as [Hin Hrest].
    simpl.
    apply andb_true_iff.
    split.
    + (* Use the helper lemma here *)
      apply evalListZClause_includes with (l := B).
      * exact Hin.
      * apply Hentails. exact Hassump.
    + apply IH.
      assumption.
Qed.

Lemma tseitin_reduced_entails :
  forall ls z p',
    IsTrue (ZProofCheck (tseitinStepRed ls z :: p')) ->
    (IsTrue (ZProofCheck p') ->
    EntailsListZCl (ZProof2Assumption p') (ZProof2ConclusionOpt p')) ->
    EntailsListZCl (ZProof2Assumption (tseitinStepRed ls z :: p'))
                   (ZProof2ConclusionOpt (tseitinStepRed ls z :: p')).
Proof.
intros.
simpl.
apply entailsAddEntails.
+
  apply SetMinusEntails with ls.
  -
    apply tseitin_check.
    simpl in *.
    apply IsTrue_and_equiv in H.
    destruct H as [H p'_true].
    apply IsTrue_and_equiv in H.
    destruct H as [H ls_true].
    assumption.
  -
    simpl in *.
    apply IsTrue_and_equiv in H.
    destruct H as [H p'_true].
    apply IsTrue_and_equiv in H.
    destruct H as [H ls_true].
    apply IsTrue_and_equiv in H.
    destruct H as [subset_true negSingletons_true].

    apply EntailsListZCl_subset with (B := ZProof2ConclusionOpt p').
    * apply H0. exact p'_true.
    * unfold IsTrue in negSingletons_true. 
      destruct (listZ3List_subset (negSingletons (setminus (TseitinProofItem2ConclusionOpt ls) z))
     (ZProof2ConclusionOpt p')) eqn:Hcmp.
      reflexivity.
      contradiction.

  -
    simpl in *.
    apply IsTrue_and_equiv in H.
    destruct H as [H p'_true].
    apply IsTrue_and_equiv in H.
    destruct H as [H ls_true].
    apply IsTrue_and_equiv in H.
    destruct H as [subset_true negSingletons_true].
    unfold IsTrue in subset_true.
    destruct (listZ3_subset z (TseitinProofItem2ConclusionOpt ls)) eqn:Hcmp.
    reflexivity. 
    contradiction.
+
  apply H0.
  apply IsTrue_andb_split in H as [Hstep Hrec].
  assumption.
Qed.

Lemma correctnessZ3ProofCheck :
  forall (p : ZProof),
    IsTrue (ZProofCheck p) ->
    EntailsListZCl (ZProof2Assumption p) (ZProof2ConclusionOpt p).
Proof.
  induction p as [| step p' IH]; intros Hcheck.
  - (* Base case: empty proof *)
    simpl in *.
    unfold EntailsListZCl.
    intros.
    assumption.

  - (* Inductive case: step :: p' *)
    destruct step.
    +
      (* Tseitin *)
      apply tseitin_entails.
      * assumption.
      * apply IH. 
    +
      (* Assumption *)
      simpl.
      apply entailsAddAssumption.
      apply IH.
      exact Hcheck.

    +
      (* RUP *)
      simpl in *.
      apply EntailsListZCl_RUP_step.
      exact Hcheck.
      apply IH.

      apply IsTrue_andb_split in Hcheck.
      destruct Hcheck as [HcL HcR].
      assumption.
   +
      (* Tseitin Reduced *)
      apply tseitin_reduced_entails.
      * assumption.
      * apply IH. 
Qed.

(*----------------------------------------------------------------------*)


Require Coq.extraction.Extraction.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction "C:\Users\harry\Documents\University\PhD\OCaml\proven_SAT_Checker.ml" ZProofCheck.

(*
Extraction "C:\Users\harry\Documents\University\PhD\OCaml\tseitinNot2For.ml" tseitinNot2For.
*)

(*
Extraction "C:\Users\harry\Documents\University\PhD\OCaml\negSingletons.ml" negSingletons.
*)


