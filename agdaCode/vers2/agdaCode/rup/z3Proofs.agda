module rup.z3Proofs where


open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny


open import rup.z3Variables
open import rup.z3Formulas
open import rup.clause
open import rup.z3BasedClause
open import rup.rupChecker


data ZProofItem : Set where
  tseitinNot : ZFor → ZProofItem
  tseitinImpElim : ZFor → ZFor → ZProofItem
  tseitinImpIntro1 : ZFor → ZFor → ZProofItem
  tseitinImpIntro2 : ZFor → ZFor → ZProofItem
  tseitinImpIntro3 : ZFor → ZFor → ZProofItem
  tseitinAndIntro   : List ZFor → ZProofItem
  tseitinAndElim   : List ZFor → ℕ → ZProofItem
  tseitinOrIntro   : List ZFor → ℕ → ZProofItem
  tseitinOrElim  : List ZFor → ZProofItem
  assumptionZ3  : List ZFor → ZProofItem
  rupZ3proof  : List ZFor → ZProofItem

ZProof : Set
ZProof = List ZProofItem


tseitinNot2For : ZFor → List ZFor
tseitinNot2For a = a ∷ notFor (notFor (negFor a)) ∷ []

tseitinImpElim2For : ZFor → ZFor → List ZFor
tseitinImpElim2For a b = negFor a ∷ b ∷ notFor(impFor a b) ∷ []

tseitinImpIntro1toFor : ZFor → ZFor → List ZFor
tseitinImpIntro1toFor a b = a ∷ impFor a b ∷ []

tseitinImpIntro2toFor : ZFor → ZFor → List ZFor
tseitinImpIntro2toFor a b = negFor b ∷ impFor a b ∷ []

tseitinImpIntro3toFor : ZFor → ZFor → List ZFor
tseitinImpIntro3toFor a b = notFor b ∷ impFor a b ∷ []



-- Original version where elements of clauses occur as in order in z3
tseitinAndIntro2ForOriginal : List ZFor → List ZFor
tseitinAndIntro2ForOriginal l = negForList l ++ (andFor l ∷ [])

-- Version in which elements in clauses are ordered so that it is easier to prove
tseitinAndIntro2ForOpt : List ZFor → List ZFor
tseitinAndIntro2ForOpt l = andFor l ∷ negForList l

tseitinAndElim2For : List ZFor → ℕ → List ZFor
tseitinAndElim2For l i = nthWithDefault i l falseFor ∷ notFor (andFor l) ∷ []

tseitinOrIntro2For : List ZFor → ℕ → List ZFor
tseitinOrIntro2For l i = negFor (nthWithDefault i l falseFor) ∷ orFor l ∷ []

-- Original version where clauses occur as in order in z3
tseitinOrElim2ForOriginal : List ZFor → List ZFor
tseitinOrElim2ForOriginal l = l ++ (notFor (orFor l) ∷ [])

-- Version in which elements in clauses are ordered so that it is easier to prove
tseitinOrElim2ForOpt : List ZFor → List ZFor
tseitinOrElim2ForOpt l = notFor (orFor l) ∷ l





ZProof2Assumption : ZProof → List (List ZFor)
ZProof2Assumption [] = []
ZProof2Assumption (assumptionZ3 x ∷ z) = x ∷ ZProof2Assumption z
ZProof2Assumption (x ∷ z) = ZProof2Assumption z



-- Original version where clauses occur as in order in z3
ZProofItem2ConclusionOriginal : ZProofItem → List ZFor
ZProofItem2ConclusionOriginal (tseitinNot a) = tseitinNot2For a
ZProofItem2ConclusionOriginal (tseitinImpElim a b) = tseitinImpElim2For a b
ZProofItem2ConclusionOriginal (tseitinImpIntro1 a b) = tseitinImpIntro1toFor a b
ZProofItem2ConclusionOriginal (tseitinImpIntro2 a b) = tseitinImpIntro2toFor a b
ZProofItem2ConclusionOriginal (tseitinImpIntro3 a b) = tseitinImpIntro3toFor a b
ZProofItem2ConclusionOriginal (tseitinAndIntro l) = tseitinAndIntro2ForOriginal l
ZProofItem2ConclusionOriginal (tseitinAndElim l i) = tseitinAndElim2For l i
ZProofItem2ConclusionOriginal (tseitinOrIntro l i) = tseitinOrIntro2For l i
ZProofItem2ConclusionOriginal (tseitinOrElim l) = tseitinOrElim2ForOriginal l
ZProofItem2ConclusionOriginal (assumptionZ3 a) = a
ZProofItem2ConclusionOriginal (rupZ3proof a) = a


ZProof2ConclusionOriginal : ZProof → List (List ZFor)
ZProof2ConclusionOriginal [] = []
ZProof2ConclusionOriginal (a ∷ l) = ZProofItem2ConclusionOriginal a ∷ ZProof2ConclusionOriginal l



-- Version in which elements in clauses are ordered so that it is easier to prove
ZProofItem2ConclusionOpt : ZProofItem → List ZFor
ZProofItem2ConclusionOpt (tseitinNot a) = tseitinNot2For a
ZProofItem2ConclusionOpt (tseitinImpElim a b) = tseitinImpElim2For a b
ZProofItem2ConclusionOpt (tseitinImpIntro1 a b) = tseitinImpIntro1toFor a b
ZProofItem2ConclusionOpt (tseitinImpIntro2 a b) = tseitinImpIntro2toFor a b
ZProofItem2ConclusionOpt (tseitinImpIntro3 a b) = tseitinImpIntro3toFor a b
ZProofItem2ConclusionOpt (tseitinAndIntro l) = tseitinAndIntro2ForOpt l
ZProofItem2ConclusionOpt (tseitinAndElim l i) = tseitinAndElim2For l i
ZProofItem2ConclusionOpt (tseitinOrIntro l i) = tseitinOrIntro2For l i
ZProofItem2ConclusionOpt (tseitinOrElim l) = tseitinOrElim2ForOpt l
ZProofItem2ConclusionOpt (assumptionZ3 a) = a
ZProofItem2ConclusionOpt (rupZ3proof a) = a


ZProof2ConclusionOpt : ZProof → List (List ZFor)
ZProof2ConclusionOpt [] = []
ZProof2ConclusionOpt (a ∷ l) = ZProofItem2ConclusionOpt a ∷ ZProof2ConclusionOpt l

ZProof2RupConclusions : ZProof → List RClause
ZProof2RupConclusions  p  = zListCl2RListCl (ZProof2ConclusionOpt p)




ZProofCheckLastStep : List RClause → ZProofItem → Bool
ZProofCheckLastStep cl (tseitinAndElim l i) = i < length l
ZProofCheckLastStep cl (tseitinOrIntro l i) = i < length l
ZProofCheckLastStep cl (rupZ3proof l) = checkOneRup cl (zCl2RClause l)
ZProofCheckLastStep cl x = true

ZProofCheck : ZProof → Bool
ZProofCheck [] = true
ZProofCheck (x ∷ p) = ZProofCheckLastStep (ZProof2RupConclusions p) x ∧b ZProofCheck p


ZProofCheckUnsat : ZProof → Bool
ZProofCheckUnsat l = ZProofCheck l ∧b (containsEmpty (ZProof2ConclusionOpt l))
