module rup.examplesRupABCDEvar   where

open import lib.boolLib
open import lib.eqLib
open import lib.finLib
open import lib.listLib
open import lib.natLib
open import lib.natLibBase
open import lib.prodLib
open import lib.unitLib
open import lib.vecLib

open import rup.variables
open import rup.clause
open import rup.model
open import rup.uResTreeProofs
open import rup.rupChecker
open import rup.rupProof
open import rup.uResTreeProofs

monikaPAss : List RClause
monikaPAss = (pos a' ∷ pos b' ∷ []) ∷
             (pos a' ∷ neg b' ∷ []) ∷
             (neg a' ∷ pos b' ∷ []) ∷
             (neg a' ∷ neg b' ∷ []) ∷ []

monikaPRup1 : RClause
monikaPRup1 = (pos b' ∷ [])

monikaPAssStep1 : List RClause
monikaPAssStep1 = monikaPRup1 ∷ monikaPAss

monikaPRup2 : RClause
monikaPRup2 = (pos a' ∷ [])

monikaPAssStep2 : List RClause
monikaPAssStep2 = monikaPRup2 ∷ monikaPAssStep1

monikaPRup3 : RClause
monikaPRup3 = []

rupCheckMonikaPStep1 : FinalRes
rupCheckMonikaPStep1  = checkOneRupWithInfo monikaPAss monikaPRup1

rupProof1 : UPrfOfFinalRes (createFullRupRClause monikaPAss monikaPRup1) (checkOneRupWithInfo monikaPAss monikaPRup1)
rupProof1 = prfChecOneRupWithInfo monikaPAss monikaPRup1



{-
uPrfOf
(res
 (res (ass (suc (suc zero))) (ass (suc (suc (suc (suc zero)))))
  (neg b') refl)
 (res (ass zero) (ass (suc (suc (suc (suc zero))))) (neg b') refl)
 (pos a') refl)
refl
-}

rupCheckMonikaPStep2 : FinalRes
rupCheckMonikaPStep2  = checkOneRupWithInfo monikaPAssStep1 monikaPRup2

rupCheckMonikaPStep3 : FinalRes
rupCheckMonikaPStep3  = checkOneRupWithInfo monikaPAssStep2 monikaPRup3

-- Initial clause
fullRupClauseMonikaPStep1 : List RClause
fullRupClauseMonikaPStep1 = createFullRupRClause monikaPAss monikaPRup1

{- result
(pos a' ∷ pos b' ∷ []) ∷
(pos a' ∷ neg b' ∷ []) ∷
(neg a' ∷ pos b' ∷ []) ∷
(neg a' ∷ neg b' ∷ []) ∷ (neg b' ∷ []) ∷ []
-}


-- initial config
initialConfigMonikaPStep1 : InitialConfig
initialConfigMonikaPStep1 = initialConfig  fullRupClauseMonikaPStep1

{- result

continue
(config
 ((pos a' ∷ pos b' ∷ []) ∷
  (pos a' ∷ neg b' ∷ []) ∷
  (neg a' ∷ pos b' ∷ []) ∷ (neg a' ∷ neg b' ∷ []) ∷ [])
 (neg b' ∷ []))

-}

oneStepResultMonikaPStep1 : ℕ  → FinalRes
oneStepResultMonikaPStep1 n = nStepsInitialConfigPropagateFinal initialConfigMonikaPStep1 n


{- applied to 0 gives
failure
(config
 ((pos a' ∷ pos b' ∷ []) ∷
  (pos a' ∷ neg b' ∷ []) ∷
  (neg a' ∷ pos b' ∷ []) ∷ (neg a' ∷ neg b' ∷ []) ∷ [])
 (neg b' ∷ []))

applied to 1 gives

failure (config [] (pos a' ∷ neg a' ∷ []))


applied to 2 gives
success
-}


monikaPFullRupProof : RFor
monikaPFullRupProof = monikaPRup1 ∷ monikaPRup2 ∷ monikaPRup3 ∷ []

corMonikaPFullRupProof : Bool
corMonikaPFullRupProof = rupProof monikaPAss monikaPFullRupProof

monikaPEntails : EntailsRFor monikaPAss monikaPFullRupProof
monikaPEntails = rupProofEntails monikaPAss monikaPFullRupProof tt

corMonikaPFullRupProofUnsat : Bool
corMonikaPFullRupProofUnsat = rupProofOfUnSat monikaPAss monikaPFullRupProof

monikaPUnSat : UnSatFor monikaPAss
monikaPUnSat = rupProofOfUnsatUnsat monikaPAss monikaPFullRupProof tt


{- ####   monikaP with one Mistake ### -}

monikaPAssWithMistake : List RClause
monikaPAssWithMistake = (pos a' ∷ pos b' ∷ []) ∷
             (pos a' ∷ neg b' ∷ []) ∷
             (neg a' ∷ neg b' ∷ []) ∷
             (neg a' ∷ neg b' ∷ []) ∷ []






rupCheckMonikaPWithMistake : FinalRes
rupCheckMonikaPWithMistake = checkOneRupWithInfo monikaPAssWithMistake monikaPRup1

-- Initial clause
fullRupClauseMonikaPWithMistake : List RClause
fullRupClauseMonikaPWithMistake = createFullRupRClause monikaPAssWithMistake monikaPRup1

-- initial config
initialConfigMonikaPWithMistake : InitialConfig
initialConfigMonikaPWithMistake = initialConfig  fullRupClauseMonikaPWithMistake

oneStepResultMonikeWithMistake : FinalRes
oneStepResultMonikeWithMistake = nStepsInitialConfigPropagateFinal initialConfigMonikaPWithMistake 1


-- initialConfigMonikaPWithMistake : InitialConfig
-- initialConfigMonikaPWithMistake
