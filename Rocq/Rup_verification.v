(*
Unit Propagation

1. Checker level:
  Takes a formula and performs Unit Propagation, returning a clause
  Empty clause infers that it was successful

2. TreeProof Level:
  Takes a formula, converts it into the TreeProof data structure.
  Performs Unit Propagation on the TreeProofs, returning a TreeProof that
  derives the empty clause if successful or nothing if not

3. Proof Level:
  For each step, a proof that a TreeProof will derive the corresponding clause
*)

(* For each level, the ordering is Checker level, TreeProof, Proof Level*)

(*--------------------------------------------------------------------------*)

(* Importing necessary libraries *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.Arith.Arith.

(*--------------------------------------------------------------------------*)

(* Datatypes *)

(* Define base Literals *)
Inductive Literal : Type :=
| pos : string -> Literal
| neg : string -> Literal.



Definition defaultLiteral : Literal := pos "defaultLiteral".

(* Function to compare two base Literals *)
Definition literal_eqb (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | pos s1, pos s2 => String.eqb s1 s2
  | neg s1, neg s2 => String.eqb s1 s2
  | _, _ => false
  end.

Definition negate (b : Literal) : Literal :=
  match b with
  | pos x => neg x
  | neg x => pos x
  end.

(* Defining clause and formula *)
Definition Clause := list Literal.
Definition Formula := list Clause.

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

(* Assumption is defined as a list of Clauses *)
Definition Assumption := Formula.

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

Lemma literal_eqb_eq : forall l1 l2 : Literal,
  literal_eqb l1 l2 = true -> l1 = l2.
Proof.
  intros l1 l2 H.
  destruct l1, l2.
  - simpl in H.
    apply String.eqb_eq in H.
    congruence.
  - simpl in H.
    discriminate H.
  - simpl in H.
    discriminate H.
  - simpl in H.
    apply String.eqb_eq in H.
    congruence.
Qed.

Lemma literal_eqb_refl : forall l1 l2 : Literal,
  l1 = l2 -> literal_eqb l1 l2 = true.
Proof.
  intros l1 l2 H.
  subst.
  destruct l2; simpl; apply String.eqb_refl.
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
Definition literal_in_seen (l : Literal) (seen : list string) : bool :=
  match l with
  | pos x => existsb (String.eqb x) seen
  | neg x => existsb (String.eqb x) seen
  end.

(* compute list of variables in a clause by adding them to seen *)
(* was update_seen_literals_in_clause *)
Fixpoint addVarsInClauseToSeen (c: Clause) (seen: list string) : list string :=
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
Fixpoint addVarsInForToSeen (f: Formula) (seen: list string) : list string :=
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

Lemma length_app_cons : forall (X : Type) (al : list X) (a : X) (n : nat),
  length al = n -> length (al ++ [a]) = S n.
Proof.
  intros X al a n H.
  rewrite app_length.
  simpl.
  rewrite H.
  apply Nat.add_1_r.
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

(* Define model as a function type from atom to bool *)
Definition Model := string -> bool.

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

Lemma models_formula_eq :
  forall (m : Model)(c : Clause)(f : Formula),
    models_formula m (c :: f) = andb (models_clause m c) (models_formula m f).
Proof.
  intros.
  reflexivity.
Qed.

(* Define the function IsTrue *)
Definition IsTrue (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.


Lemma IsTrue2EqTrue : forall (b : bool), IsTrue b -> b = true.
Proof.
intros b H0.
destruct b.
reflexivity.
unfold IsTrue in H0.
contradiction.
Qed.


Definition Models_literal (m : Model) (l : Literal) : Prop :=
  IsTrue (models_literal m l).

Definition Models_clause (m : Model) (c : Clause) : Prop :=
  IsTrue (models_clause m c).

Definition Models_formula (m : Model) (f : Formula) : Prop :=
  IsTrue (models_formula m f).

Definition entails (f : Formula) (c : Clause) : Prop :=
  (forall (m : Model),
      Models_formula m f -> Models_clause m c).

Definition entailsF (f : Formula) (f' : list Clause) : Prop :=
  (forall (m : Model),
    Models_formula m f -> Models_formula m f').
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

Lemma IsTrue_and' : forall a b : bool,
    a && b = true -> IsTrue a /\ IsTrue b.
Proof.
  intros a b H.
  destruct a.
  destruct b.
  split.
  exact I.
  exact I.
  split.
  exact I.
  unfold andb in H.
  discriminate H.
  unfold andb in H.
  discriminate H.
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

Lemma lit_eq_dec : forall a b : Literal, {a = b} + {a <> b}.
Proof.
   intros a b.
   destruct a as [s1 | s1]; destruct b as [s2 | s2].
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
   - right. intro H. inversion H.
   - right. intro H. inversion H.
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.

Lemma literal_eqb_spec :
  forall x y, reflect (x = y) (literal_eqb x y).
Proof.
  intros [sx|sx] [sy|sy]; simpl;
  try (apply ReflectF; discriminate).
  - destruct (String.eqb_spec sx sy).
    + subst. apply ReflectT. reflexivity.
    + apply ReflectF. congruence.
  - destruct (String.eqb_spec sx sy).
    + subst. apply ReflectT. reflexivity.
    + apply ReflectF. congruence.
Qed.

Lemma remove_l_from_cons_l : forall
(ls : list Literal)
(l : Literal), ((removeLitFromClause l (l :: ls)) =
(removeLitFromClause l ls)).
Proof.
intros.
cbn.
destruct (lit_eq_dec l l) as [H | H] eqn:Ha.
+ destruct (literal_eqb_spec l l) as [Heq | Hneq].
  - reflexivity. (* because the if-branch is the same as the RHS *)
  - contradiction. (* l = l, so this branch is impossible *)
+ contradiction.
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

(* Example usage *)
Definition example_literals : list Literal := [pos "a"; neg "b"; pos "c"].
Definition example_literal : Literal := pos "a".
Compute compare_outputs example_literals example_literal.

Definition example_literals2 : list Literal := [neg "a"; neg "b"; pos "c"].
Definition example_literal2 : Literal := pos "a".
Compute compare_outputs example_literals2 example_literal2.


(* #####  from Logical_Entailment.v #### *)

Definition negate_clause (c : Clause) : Formula :=
  map (fun l => [negate l]) c.


Lemma emptyClauseNotModelled : forall (m :  Model) , not (Models_clause m []).
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
  simpl in H.
  assumption.
  simpl in H0.
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
  pose proof (bImplModelsEmptyImpliesNotbaux b m H) as H0a.
  destruct b.
  simpl in H0a.
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

unfold not.
intros.
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

Lemma simplify_false : forall (m : Model) (a : string) (A : Formula) (B : bool)
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

Lemma simplify_false_reverse : forall (m : Model) (a : string) (A : Formula) (B : bool)
 (xs : Clause),
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

Lemma simplify_falsity_equivalence : forall (m : Model) (a : string) (A : Formula) (B : bool)
(xs : Clause),
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

  destruct (m s) eqn:Hma.
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

  destruct (m s) eqn:Hma.
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
    intros H. unfold not. intros F. contradiction.
Qed.

(* Function to transform a clause into a list of clauses with negated literals *)


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
(*TESTING*)

(* Define individual clauses as literals, some of which are AtomicClauses *)
Definition clause1 : Clause := [pos "a"; pos "b"].  (* a ∨ b *)
Definition clause2 : Clause := [pos "a"; neg "b"].  (* a ∨ ¬b *)
Definition clause3 : Clause := [neg "a"; pos "b"].  (* ¬a ∨ b *)
Definition clause4 : Clause := [neg "a"; neg "b"].  (* ¬a ∨ ¬b *)
Definition rup1 : Clause := [pos "b"].
Definition rup2 : Clause := [pos "a"].

Definition M : Formula := [clause1; clause2; clause3; clause4; rup1].

Compute unitPropagationAndCheck M.

(* Define individual clauses as literals, some of which are AtomicClauses *)
Definition clause1' : Clause := [pos "a"; pos "b"].
Definition clause2' : Clause := [neg "b"; pos "c"].
Definition clause3' : Clause := [neg "c"].

Definition M' : Formula := [clause1'; clause2'; clause3'].
Compute unitPropagationAndCheck M'.

Definition Hclause1 : Clause := [pos "a"].
Definition Hclause2 : Clause := [neg "a"; pos "b"].
Definition Hclause3 : Clause := [neg "a"; neg "b"].
Definition Hclause4 : Clause := [pos "b"; pos "c"].
Definition H : Formula := [Hclause1; Hclause2; Hclause3; Hclause4].

Compute unitPropagationAndCheck H.

(*--------------------------------------------------------------------------*)

Compute unitPropagationAndCheckWithAssProof [[pos "a"]; [neg "a"]].

Compute unitPropagationAndCheckWithAssProof [[pos "a"; pos "b"]; [neg "b"];[neg "a"]].

Compute unitPropagationAndCheckWithAssProof M'.

Definition tc0 : Clause := [pos "a"; pos "b"].
Definition tc1 : Clause := [neg "a"].
Definition as0 : Assumption := [tc0; tc1].
Definition tp0 : list TreeProof := [ass 0; ass 1].

Compute unitPropagationAndCheckWithAssProof H.

Inductive RupProofStep  : Type :=
| ass'  : Clause -> RupProofStep
| rup' : Clause -> RupProofStep.

Definition RupProof : Type := list RupProofStep.

Fixpoint rupProof2Assumptions (pl : RupProof) : list Clause :=
  match pl with
  | [] => []
  | (p :: pl) =>
      match p with
      | ass' c => c :: rupProof2Assumptions pl
      | rup' c => rupProof2Assumptions pl
      end
  end.

Definition rupProof2AssumptionsRevFirst (pl : RupProof) : list Clause :=
     rupProof2Assumptions (rev pl).

Lemma rupProof2AssumptionsEqass :
  forall (c : Clause)(pl : RupProof),
    rupProof2Assumptions ((ass' c) :: pl) = c :: rupProof2Assumptions pl.
Proof.
  intros.
  reflexivity.
Qed.


Lemma rupProof2AssumptionsEqrup :
  forall (c : Clause)(pl : RupProof),
    rupProof2Assumptions ((rup' c) :: pl) = rupProof2Assumptions pl.
Proof.
  intros.
  reflexivity.
Qed.


Fixpoint rupProof2Conclusions (pl : RupProof) : list Clause :=
  match pl with
  | [] => []
  | (p :: pl) =>
      match p with
      | ass' c => c :: rupProof2Conclusions pl
      | rup' c => c :: rupProof2Conclusions pl
      end
  end.

Definition rupProof2ConclusionsRevFirst (pl : RupProof) : list Clause :=
     rupProof2Conclusions (rev pl).

Lemma rupProof2ConclusionsEqass :
  forall (c : Clause)(pl : RupProof),
    rupProof2Conclusions ((ass' c) :: pl) = c :: rupProof2Conclusions pl.
Proof.
  intros.
  reflexivity.
Qed.


Lemma rupProof2ConclusionsEqrup :
  forall (c : Clause)(pl : RupProof),
    rupProof2Conclusions ((rup' c) :: pl) = c :: rupProof2Conclusions pl.
Proof.
  intros.
  reflexivity.
Qed.



Fixpoint rupProofChecker (pl : RupProof) : bool :=
  match pl with
  | [] => true
  | (p :: pl) =>
      match p with
      | ass' c => rupProofChecker pl
      | rup' c => RUP_Checker (rupProof2Conclusions pl) c &&
                    rupProofChecker pl
      end
  end.

(* as rupProofChecker but reverts first the list since
   the input files need to be read in reverse order
   since they are processed by Rocq from the inside (last element first) *)

Definition rupProofCheckerRevFirst (pl : RupProof) : bool :=
   rupProofChecker (rev pl).

Lemma rupProofCheckerEqass :
  forall (c : Clause)(pl : RupProof),
    rupProofChecker ((ass' c)  :: pl) = rupProofChecker pl.
Proof.
  intros.
  reflexivity.
Qed.

Lemma rupProofCheckerEqrup :
  forall (c : Clause)(pl : RupProof),
    rupProofChecker ((rup' c)  :: pl) =
        RUP_Checker (rupProof2Conclusions pl) c &&
                    rupProofChecker pl.
Proof.
  intros.
  reflexivity.
Qed.



Lemma RUProofCheckerCorrect1 :
  forall  (pl : RupProof),
    rupProofChecker pl = true -> entailsF (rupProof2Assumptions pl)
                                   (rupProof2Conclusions pl).
Proof.
  intros pl q.
  induction pl.
  unfold rupProof2Assumptions.
  unfold rupProof2Conclusions.
  unfold entailsF.
  intros.
  assumption.
  induction a.
  rewrite (rupProof2AssumptionsEqass c pl).
  rewrite (rupProof2ConclusionsEqass c pl).
  unfold entailsF.
  intros.
  unfold Models_formula.
  rewrite (models_formula_eq  m c  (rupProof2Conclusions pl)).
  apply IsTrue_and_reverse.
  split.
  rewrite (rupProofCheckerEqass c pl) in q.
  apply IHpl in q.
  unfold entailsF in q.
  unfold Models_formula in H0.
  rewrite (models_formula_eq m c (rupProof2Assumptions pl)) in H0.
  apply IsTrue_and in H0.
  destruct H0 as [H01 H02].
  assumption.
  unfold Models_formula.
  rewrite (rupProofCheckerEqass c pl) in q.
  apply IHpl in q.
  unfold entailsF in q.
  unfold Models_formula in H0.
  rewrite (models_formula_eq m c (rupProof2Assumptions pl)) in H0.
  apply IsTrue_and in H0.
  destruct H0 as [H01 H02].
  unfold entailsF in IHpl.
  specialize (q m).
  apply q in H02.
  assumption.
  rewrite (rupProof2AssumptionsEqrup c pl).
  rewrite (rupProof2ConclusionsEqrup c pl).
  unfold entailsF.
  intros.
  unfold Models_formula.
  rewrite (models_formula_eq  m c  (rupProof2Conclusions pl)).
  apply IsTrue_and_reverse.
  split.
  rewrite (rupProofCheckerEqrup c pl) in q.
  apply IsTrue_and' in q.
  destruct q as [q0 q1].
  apply IsTrue2EqTrue in q0.
  apply RUP_Checker_correct in q0.
  unfold entails in q0.
  specialize (q0 m).
  apply IsTrue2EqTrue in q1.
  apply IHpl in q1.
  unfold entailsF in q1.
  specialize (q1 m).
  apply q1 in H0.
  apply q0 in H0.
  unfold Models_clause in H0.
  assumption.
  unfold Models_clause in H0.
  rewrite (rupProofCheckerEqrup c pl) in q.
  apply IsTrue_and' in q.
  destruct q as [q0 q1].
  apply IsTrue2EqTrue in q1.
  apply IHpl in q1.
  unfold entailsF in q1.
  specialize (q1 m).
  apply q1 in H0.
  unfold Models_formula in H0.
  assumption.
Qed.


Definition IsEmpty  (c : Clause ) : bool :=
  match c with
  | [] => true
  | (x :: c) => false
  end.


Fixpoint ContainsEmpty (l : list Clause) : bool :=
  match l with
  | [] => false
  | (c :: l) => IsEmpty c || ContainsEmpty l
  end.

Lemma ContainsEmpty_Eqempty :
  forall (l : list Clause) ,    ContainsEmpty ([] :: l) = true.
Proof.
  intros l.
  reflexivity.
Qed.

Lemma ContainsEmpty_EqNonEmpty :
  forall (l : Literal)(c : Clause)(f : list Clause) ,
  ContainsEmpty ((l :: c) :: f) = ContainsEmpty f.
Proof.
  intros c l.
  reflexivity.
Qed.



Definition rupProofCheckerUnsat (pl : RupProof) : bool :=
  rupProofChecker pl && ContainsEmpty (rupProof2Conclusions pl).


(* as rupProofCheckerUnSat but reverts first the list since
   the input files need to be read in reverse order
   since they are processed by Rocq from the inside (last element first) *)

Definition rupProofCheckerUnsatRevFirst (pl : RupProof) : bool :=
   rupProofCheckerUnsat (rev pl).


Definition UnsatClause (c : Clause): Prop :=
  forall (m : Model), not (Models_clause m c).

Definition UnSatFor (f : Formula): Prop :=
  forall (m : Model), not (Models_formula m f).


Lemma transferEntailsFUnsat :
  forall (f f' : Formula),
    entailsF f f' -> UnSatFor f' -> UnSatFor f.
Proof.
  intros f f' ff' notf'.
  unfold entailsF in ff'.
  unfold UnSatFor in notf'.
  unfold UnSatFor.
  intros m mf.
  specialize (ff' m).
  specialize (notf' m).
  apply ff' in mf.
  apply notf' in mf.
  assumption.
Qed.

Lemma unsatEmtpyClause : UnsatClause [].
Proof.
  unfold UnsatClause.
  intros m p.
  unfold Models_clause  in p.
  unfold models_clause  in p.
  contradiction.
Qed.

Lemma UnSatForEqNonEmptyHead :
  forall (a : Literal)(a0 : Clause)(f : Formula),
    UnSatFor f -> UnSatFor ((a :: a0) :: f).
Proof.
  intros.
  unfold UnSatFor.
  intros m mf.
  unfold UnSatFor in H0.
  specialize (H0 m).
  unfold Models_formula in mf.
  rewrite  models_formula_eq in mf.
  apply IsTrue_and in mf.
  destruct mf as [mf0 mf1].
  unfold Models_formula in H0.
  contradiction.
Qed.


Lemma unsatFormulaWithEmpty :
  forall (f : Formula),
    ContainsEmpty f = true -> UnSatFor f.
Proof.
  intros f p.
  induction f.
  unfold UnSatFor.
  intros m q.
  unfold ContainsEmpty in p.
  discriminate p.
  induction a.
  unfold UnSatFor.
  intros m q.
  unfold Models_formula in q.
  rewrite (models_formula_eq m [] f) in q.
  apply IsTrue_and in q.
  destruct q as [q0 q1].
  unfold models_clause in q0.
  unfold IsTrue in q0.
  contradiction.
  (* p : ContainsEmpty ((a :: a0) :: f) = true *)
  rewrite ContainsEmpty_EqNonEmpty in p.
  apply IHf in p.
  apply UnSatForEqNonEmptyHead.
  assumption.
Qed.

Lemma RupProofcheckerUnSat :
  forall (pl : RupProof), rupProofCheckerUnsat pl = true
                          -> UnSatFor (rupProof2Assumptions pl).
Proof.
  intros pl checktrue.
  unfold rupProofCheckerUnsat in checktrue.
  apply IsTrue_and' in checktrue.
  destruct checktrue as [ check1 check2 ].
  apply IsTrue2EqTrue in check1.
  apply RUProofCheckerCorrect1 in check1.
  apply IsTrue2EqTrue in check2.
  apply unsatFormulaWithEmpty in check2.
  apply (transferEntailsFUnsat (rupProof2Assumptions pl) (rupProof2Conclusions pl)).
  assumption.
  assumption.
Qed.



(* ------------------ NOT FOR GIT ------------------------------- *)
Definition anton_tseitinExample12 : RupProof :=
     [ (ass' [ pos "a" ; pos "b"; pos "c" ]) ;
        (ass' [ neg "a" ]) ;
        (ass' [ neg "b" ]) ;
        (ass' [ neg "c" ]) ;
        (rup' []) ].

Compute (rupProofCheckerRevFirst  anton_tseitinExample12).
Compute (rupProofCheckerUnsatRevFirst  anton_tseitinExample12).

Definition anton_tseitinExample13 : RupProof :=
      [ (ass' [ (neg "a" ) ; pos "b" ]);
        (ass' [ (neg "b" ) ; pos "c" ]);
        (ass' [ (neg "c" ) ; pos "d" ]) ;
        (ass' [ neg "a" ; neg "d" ]);
        (ass' [ pos "a" ; pos "b" ]);
        (ass' [ neg "d" ; pos "a" ]);
        (rup' [ pos "b" ]);
        (rup' [ pos "c" ]);
        (rup' [ pos "d" ]);
        (rup' [ neg "a" ]);
        (rup' []) ].

Compute (rupProofCheckerRevFirst  anton_tseitinExample13).
Compute (rupProofCheckerUnsatRevFirst  anton_tseitinExample13).




(*

Testing

Definition anton_tseitinExample13a : RupProof :=
  rev [ (ass' [ (neg "a" ) ; pos "b" ]);
        (ass' [ (neg "b" ) ; pos "c" ]);
        (ass' [ (neg "c" ) ; pos "d" ]) ;
        (ass' [ neg "a" ; neg "d" ]);
        (ass' [ pos "a" ; pos "b" ]);
        (ass' [ neg "d" ; pos "a" ]);
        (rup' [ pos "b" ]);
        (rup' [ pos "c" ]);
        (rup' [ pos "d" ]);
        (rup' [ neg "a" ])].




Compute (rupProofChecker  anton_tseitinExample13a).
Compute (rupProof2Assumptions anton_tseitinExample13a).
Compute (rupProof2Conclusions anton_tseitinExample13a).
Compute (RUP_Checker (rupProof2Assumptions anton_tseitinExample13a) []).
Compute (unitPropagationAndCheck (rupProof2Conclusions anton_tseitinExample13a)).
Compute (iteratePropagator 0 (splitClauses (rupProof2Conclusions anton_tseitinExample13a))).

 *)


(*  Functions needed for the full checker which  only uses the rupProofChecker
 *)


Inductive proofStep : Type :=
| Tseitin' : Clause -> proofStep
| Rup' : Clause -> proofStep
| Assumption' : Clause -> proofStep
| Deletion' : Clause -> proofStep.

Fixpoint appendFor (f g : Formula) : Formula :=
  match f with
  | [] => g
  | (c :: f1) => c :: (appendFor f1 g)
  end.

Fixpoint removeClauseFromFor (c : Clause) (f : Formula) : Formula :=
  match f with
  | [] => []
  | hd :: tl =>
      let new_formula := removeClauseFromFor c tl in
      if clause_eqb c hd then new_formula
      else hd :: new_formula
  end.


Fixpoint checkProof (p : list proofStep) (f : Formula) : bool * option proofStep :=
  match p with
  | [] => (true, None)
  | (step :: ps) =>
    match step with
     | Tseitin' c => checkProof ps (appendFor f  (c :: []))
     | Rup' c =>
       match RUP_Checker f c with
        | true => checkProof ps (appendFor f (c ::  []))
        | false => (false, (Some step))
       end
    | Assumption' a => checkProof ps (appendFor f (a :: []))
    | Deletion' c => checkProof ps (removeClauseFromFor c f)
    end
end.






Require Extraction.

Extraction "RupProofChecker"  rupProofChecker checkProof proofStep rupProofCheckerRevFirst rupProofCheckerUnsatRevFirst rupProof2ConclusionsRevFirst rupProof2AssumptionsRevFirst.
