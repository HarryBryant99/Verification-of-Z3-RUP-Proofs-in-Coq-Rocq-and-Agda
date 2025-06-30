open import Data.String

open import lib.boolLib
open import lib.listLibAny
open import lib.natLibBase
open import lib.emptyLib
open import lib.unitLib

open import rup.z3Formulas
open import rup.z3Model
open import rup.z3Proofs
open import rup.z3ProofCorrect

currentProof : ZProof
currentProof =
  (rupZ3proof ([]) ) ∷ 
  (rupZ3proof ((notFor (zvar "y" )) ∷ []) ) ∷ 
  (rupZ3proof ((zvar "x" ) ∷ []) ) ∷ 
  (rupZ3proof ((impFor (zvar "y" ) (zvar "x" ) ) ∷ []) ) ∷ 
  (rupZ3proof ((impFor (zvar "x" ) (zvar "y" ) ) ∷ []) ) ∷ 
  (rupZ3proof ((andFor ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) ) ∷ []) ) ∷ 
  (assumptionZ3 ((notFor (zvar "z" )) ∷ []) ) ∷ 
  (assumptionZ3 ((andFor ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) ) ∷ (zvar "z" ) ∷ []) ) ∷ 
  (tseitinAndIntro ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) ) ∷ 
  (tseitinAndElim ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) 3 ) ∷ 
  (tseitinAndElim ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) 2 ) ∷ 
  (tseitinAndElim ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) 1 ) ∷ 
  (tseitinAndElim ((impFor (zvar "x" ) (zvar "y" ) ) ∷ (impFor (zvar "y" ) (zvar "x" ) ) ∷ (zvar "x" ) ∷ (notFor (zvar "y" )) ∷ []) 0 ) ∷ 
  (tseitinImpIntro2 (zvar "y" ) (zvar "x" ) ) ∷ 
  (tseitinImpIntro1 (zvar "y" ) (zvar "x" ) ) ∷ 
  (tseitinImpIntro2 (zvar "x" ) (zvar "y" ) ) ∷ 
  (tseitinImpIntro1 (zvar "x" ) (zvar "y" ) ) ∷ 
  (tseitinImpElim (zvar "x" ) (zvar "y" ) ) ∷ 
  []
assumptions : List (List ZFor)
assumptions = ZProof2Assumption currentProof

conclusions : List (List ZFor)
conclusions = ZProof2ConclusionOpt currentProof

checkProof : Bool
checkProof = ZProofCheck currentProof

checkProofUnSat : Bool
checkProofUnSat = ZProofCheckUnsat currentProof

-- applying the following to tt often crashes agda
UnSatCurrentProof : atom checkProofUnSat  → UnSat (ZProof2Assumption currentProof)
UnSatCurrentProof = correctenessZ3ProofCheckUnsat currentProof
