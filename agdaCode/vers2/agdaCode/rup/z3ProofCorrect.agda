module rup.z3ProofCorrect where


open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny
open import lib.unitLib



open import rup.z3Variables
open import rup.z3Formulas
open import rup.clause
open import rup.rupProof
open import rup.z3BasedClause
open import rup.rupChecker
open import rup.model
open import rup.z3Model
open import rup.z3Proofs

notNegForEq : (mod : ZModel)(x : ZFor) → evalZFor mod (negFor x) ≡ not (evalZFor mod x)
notNegForEq mod (zvar x) = refl
notNegForEq mod (andFor x) = refl
notNegForEq mod (orFor x) = refl
notNegForEq mod (impFor x x₁) = refl
notNegForEq mod (notFor x) = doubleNotAtom₁' (evalZFor mod x)
notNegForEq mod trueFor = refl
notNegForEq mod falseFor = refl

negForListEq : (mod : ZModel)(l : List ZFor)
     → evalListZFor mod (negForList l) ≡ mapList not  (evalListZFor mod l)
negForListEq mod [] = refl
negForListEq mod (x ∷ l) rewrite (notNegForEq mod x) rewrite (negForListEq mod l) = refl

tseitinNotTautaux : (a : Bool) → T (a ∨b (not (not (not a)) ∨b false))
tseitinNotTautaux false = tt
tseitinNotTautaux true = tt

tseitinNotTaut : (x : ZFor) → ZTaut (tseitinNot2For x)
tseitinNotTaut x mod rewrite (notNegForEq mod x) = tseitinNotTautaux (evalZFor mod x)

-------------

tseitinImpElimTautaux : (x y : Bool) →
              T  (not x ∨b (y ∨b (not (not x ∨b y) ∨b false)))
tseitinImpElimTautaux false y = tt
tseitinImpElimTautaux true false = tt
tseitinImpElimTautaux true true = tt


tseitinImpElimTaut : (x y : ZFor) → ZTaut (tseitinImpElim2For x y)
tseitinImpElimTaut x y mod rewrite (notNegForEq mod x) = tseitinImpElimTautaux (evalZFor mod x)  (evalZFor mod y)

tseitinImpIntro1Tautaux : (x y : Bool) →
      T   (x ∨b  ((not (x) ∨b y) ∨b false))
tseitinImpIntro1Tautaux false y = tt
tseitinImpIntro1Tautaux true y = tt

tseitinImpIntro1Taut : (x y : ZFor) → ZTaut (tseitinImpIntro1toFor x y)
tseitinImpIntro1Taut x y mod = tseitinImpIntro1Tautaux (evalZFor mod x) (evalZFor mod y)

tseitinImpIntro2Tautaux : (x y : Bool) →
    T (not y ∨b ((not x ∨b y) ∨b false))
tseitinImpIntro2Tautaux false false = tt
tseitinImpIntro2Tautaux false true = tt
tseitinImpIntro2Tautaux true false = tt
tseitinImpIntro2Tautaux true true = tt

tseitinImpIntro2Taut : (x y : ZFor) → ZTaut (tseitinImpIntro2toFor x y)
tseitinImpIntro2Taut x y mod rewrite (notNegForEq mod y) = tseitinImpIntro2Tautaux (evalZFor mod x) (evalZFor mod y)

tseitinImpIntro3Tautaux : (x y : Bool) → T  (not y ∨b ((not x ∨b y) ∨b false))
tseitinImpIntro3Tautaux x false = tt
tseitinImpIntro3Tautaux false true = tt
tseitinImpIntro3Tautaux true true = tt

tseitinImpIntro3Taut : (x y : ZFor) → ZTaut (tseitinImpIntro3toFor x y)
tseitinImpIntro3Taut x y mod = tseitinImpIntro3Tautaux (evalZFor mod x) (evalZFor mod y)

tseitinAndIntroTautaux : (l : List Bool)
   → T  (andListBool l ∨b
          orListBool (mapList not l))
tseitinAndIntroTautaux [] = tt
tseitinAndIntroTautaux (false ∷ l) = tt
tseitinAndIntroTautaux (true ∷ l) = tseitinAndIntroTautaux l


tseitinAndIntroTaut : (l : ZClause) → ZTaut (tseitinAndIntro2ForOpt l)
tseitinAndIntroTaut l mod rewrite (negForListEq mod l) = tseitinAndIntroTautaux (evalListZFor mod l)

tseitinAndElimTautaux1 : (x y : Bool)
        → T (x ∨b (not (x ∧b y) ∨b  false))
tseitinAndElimTautaux1 false y = tt
tseitinAndElimTautaux1 true y = tt


tseitinAndElimTautaux2 : (x y z : Bool)
    → T (x ∨b (not z ∨b false))
    → T ( x ∨b (not (y ∧b z) ∨b  false))
tseitinAndElimTautaux2 false false z u = tt
tseitinAndElimTautaux2 true false z u = tt
tseitinAndElimTautaux2 false true false u = tt
tseitinAndElimTautaux2 true true z u = tt


tseitinAndElimTaut : (l : ZClause)(i : ℕ)(il : atom (i < length l) ) → ZTaut (tseitinAndElim2For l i)
tseitinAndElimTaut (x ∷ l) zero il mod = tseitinAndElimTautaux1 (evalZFor mod x ) (andListBool (evalListZFor mod l))
tseitinAndElimTaut (x ∷ l) (suc i) il mod =
      tseitinAndElimTautaux2
          (evalZFor mod (nthWithDefault i l falseFor))
          (evalZFor mod x) (andListBool (evalListZFor mod l))
          (tseitinAndElimTaut l i il mod)


tseitinOrIntroTautaux1 : (x y : Bool)
                        → T (not x ∨b ((x ∨b y) ∨b false))
tseitinOrIntroTautaux1 false y = tt
tseitinOrIntroTautaux1 true y = tt

tseitinOrIntroTautaux2 : (x y z : Bool)
    → T  (x ∨b (y ∨b false))
    →  T (x ∨b ((z ∨b y) ∨b false))
tseitinOrIntroTautaux2 false true false p = tt
tseitinOrIntroTautaux2 false true true p = tt
tseitinOrIntroTautaux2 true y z p = tt



tseitinOrIntroTaut : (l : ZClause)(i : ℕ)(il : atom (i < length l) ) → ZTaut (tseitinOrIntro2For l i)
tseitinOrIntroTaut (x ∷ l) zero il mod rewrite (notNegForEq mod x)
         = tseitinOrIntroTautaux1 (evalZFor mod x)
                                  (orListBool (evalListZFor mod l))
tseitinOrIntroTaut (x ∷ l) (suc i) il mod = tseitinOrIntroTautaux2
                                              (evalZFor mod (negFor (nthWithDefault i l falseFor)))
                                              (orListBool (evalListZFor mod l)) (evalZFor mod x)
                                              (tseitinOrIntroTaut l i il mod)


tseitinOrElimTautaux : (l : List Bool)
   →   T  (not (orListBool l) ∨b orListBool l)
tseitinOrElimTautaux l = tertimumNonDbool (orListBool l)

--

tseitinOrElimTaut : (l : ZClause) → ZTaut (tseitinOrElim2ForOpt l)
tseitinOrElimTaut l mod = tseitinOrElimTautaux (evalListZFor mod l)




correctnessZ3ProofCheck : (p : ZProof)
                          → IsTrue (ZProofCheck p)
                          → EntailsListZCl (ZProof2Assumption p) (ZProof2ConclusionOpt p)
correctnessZ3ProofCheck [] q mod x = x
correctnessZ3ProofCheck (tseitinNot x ∷ p) q = entailsAddTaut (tseitinNot2For x) (tseitinNotTaut  x) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinImpElim x y ∷ p) q = entailsAddTaut (tseitinImpElim2For x y) (tseitinImpElimTaut x y) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinImpIntro1 x y ∷ p) q = entailsAddTaut (tseitinImpIntro1toFor x y) (tseitinImpIntro1Taut x y) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinImpIntro2 x y ∷ p) q = entailsAddTaut (tseitinImpIntro2toFor x y) (tseitinImpIntro2Taut x y) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinImpIntro3 x y ∷ p) q = entailsAddTaut (tseitinImpIntro3toFor x y) (tseitinImpIntro3Taut x y) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinAndIntro l ∷ p) q = entailsAddTaut (tseitinAndIntro2ForOpt l) (tseitinAndIntroTaut l) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (tseitinAndElim l i ∷ p) q = entailsAddTaut (tseitinAndElim2For l i) (tseitinAndElimTaut l i (∧b-elim1 (i < length l) (ZProofCheck p) q )) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p
                                                     (∧b-elim2 (i < length l) (ZProofCheck p) q ))
correctnessZ3ProofCheck (tseitinOrIntro l i ∷ p) q = entailsAddTaut (tseitinOrIntro2For l i) (tseitinOrIntroTaut l i (∧b-elim1 (i < length l) (ZProofCheck p) q )) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p
                                                     (∧b-elim2 (i < length l) (ZProofCheck p) q ))
correctnessZ3ProofCheck (tseitinOrElim l ∷ p) q = entailsAddTaut (tseitinOrElim2ForOpt l) (tseitinOrElimTaut l) (ZProof2Assumption p) (ZProof2ConclusionOpt p) (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (assumptionZ3 x ∷ p) q = entailsAddAss (ZProof2Assumption p) (ZProof2ConclusionOpt p) x
                                                       (correctnessZ3ProofCheck p q)
correctnessZ3ProofCheck (rupZ3proof cl ∷ p) q =
     let
         p1 : T (checkOneRup (ZProof2RupConclusions p) (zCl2RClause cl))
         p1 = ∧b-elim1 (checkOneRup (ZProof2RupConclusions p) (zCl2RClause cl)) (ZProofCheck p) q

         p1' : EntailsRCl (zListCl2RListCl (ZProof2ConclusionOpt p)) (zCl2RClause cl)
         p1' = rupCorrect (ZProof2RupConclusions p) (zCl2RClause cl) p1

         p1'' : EntailsZCl   (ZProof2ConclusionOpt p) cl
         p1'' = entailsRCl2ZCl (ZProof2ConclusionOpt p) cl p1'

         p2 : T (ZProofCheck p)
         p2 = ∧b-elim2 (checkOneRup (ZProof2RupConclusions p) (zCl2RClause cl)) (ZProofCheck p) q

         ih : EntailsListZCl (ZProof2Assumption p) (ZProof2ConclusionOpt p)
         ih = correctnessZ3ProofCheck p p2


     in   entailsZCladdInference (ZProof2Assumption p)
          (ZProof2ConclusionOpt p) cl ih  p1''


correctenessZ3ProofCheckUnsat : (p : ZProof)
                                → IsTrue (ZProofCheckUnsat p)
                                → UnSat (ZProof2Assumption p)
correctenessZ3ProofCheckUnsat p q =
    let
        proofch : T (ZProofCheck p)
        proofch  = ∧b-elim1 (ZProofCheck p) (containsEmpty (ZProof2ConclusionOpt p)) q

        empt : ContainsEmpty (ZProof2ConclusionOpt p)
        empt  = ∧b-elim2 (ZProofCheck p) (containsEmpty (ZProof2ConclusionOpt p)) q

        entails : EntailsListZCl (ZProof2Assumption p) (ZProof2ConclusionOpt p)
        entails = correctnessZ3ProofCheck p proofch

        unsatConc : UnSat (ZProof2ConclusionOpt p)
        unsatConc = containsEmptyUnSat (ZProof2ConclusionOpt p) empt

    in entailsUnSatUnSat (ZProof2Assumption p) (ZProof2ConclusionOpt p) entails unsatConc
