module rup.uResTreeProofsDisplay where

open import lib.boolLib
open import lib.emptyLib
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

data UPrfDisplay : Set where
  ass : RClause →  UPrfDisplay
  res : (t1 t2 : UPrfDisplay) → RClause → UPrfDisplay


uPrfDisplay : (as : RFor) → UPrf as → UPrfDisplay
uPrfDisplay as (ass i) = ass (nthFin as i)
uPrfDisplay as (res p q l ur) = res (uPrfDisplay as p) (uPrfDisplay as q) ((conclusionUR as  p) \\ (negRLit l))

uprfOfDisplay : (as : RFor)(c : RClause) → UPrfOf as c → UPrfDisplay
uprfOfDisplay as c p = uPrfDisplay as (p .prf)

UPrfDisplayFor : Set
UPrfDisplayFor = List UPrfDisplay



uPrfDisplayFor : (as : RFor)(cl : RFor) → (UPrfOfFor as cl) → UPrfDisplayFor
uPrfDisplayFor as [] p = []
uPrfDisplayFor as (c ∷ cl) (π p1 prest) = uprfOfDisplay as c p1 ∷ uPrfDisplayFor as cl prest


uPrfDisplayLits : (as : RFor)(ls : List RLit) → (UPrfOfLits as ls) → UPrfDisplayFor
uPrfDisplayLits as [] p = []
uPrfDisplayLits as (l ∷ ls) (π p1 prest) = uprfOfDisplay as (lit2RClause l) p1 ∷ uPrfDisplayLits as ls prest

UPrfOfConfigDisplay : Set
UPrfOfConfigDisplay = UPrfDisplayFor × UPrfDisplayFor

uprfOfConfigDisplay : (as : RFor)(cfg : Config) → UPrfOfConfig as cfg → UPrfOfConfigDisplay
uprfOfConfigDisplay as (config nunitCl unitCl) (π prfNunitCl prfUnitCl) = π (uPrfDisplayFor as nunitCl prfNunitCl) (uPrfDisplayLits as unitCl prfUnitCl)

data UPrfOfFinalResDisplay : Set where
  failure : UPrfOfConfigDisplay → UPrfOfFinalResDisplay
  continue : UPrfOfConfigDisplay → UPrfOfFinalResDisplay
  success  : UPrfDisplay → UPrfOfFinalResDisplay

uPrfOfFinalResDisplay : (as : RFor)(p : FinalRes) → UPrfOfFinalRes as p → UPrfOfFinalResDisplay
uPrfOfFinalResDisplay as (failure (config nunitCl unitCl)) q = failure (uprfOfConfigDisplay as (config nunitCl unitCl) q)
uPrfOfFinalResDisplay as (continue (config nunitCl unitCl)) q = continue (uprfOfConfigDisplay as (config nunitCl unitCl) q)
uPrfOfFinalResDisplay as success q = success (uprfOfDisplay as [] q)

prfCheckOneRupWithInfoDisplay : (as : RFor)(c : RClause) → UPrfOfFinalResDisplay
prfCheckOneRupWithInfoDisplay as c = let
                                      resultProof : UPrfOfFinalRes
                                                    (createFullRupRClause as c)
                                                    (checkOneRupWithInfo as c)
                                      resultProof = prfChecOneRupWithInfo as c


                                     in uPrfOfFinalResDisplay (createFullRupRClause as c) (checkOneRupWithInfo as c) resultProof
-- prfChecOneRupWithInfo as rp

{-
uprfOfConfigDisplay as (config nunitCl unitCl) p .fst = uPrfDisplayFor as nunitCl {!!}
uprfOfConfigDisplay as (config nunitCl unitCl) p .snd = {!uPrfDisplayLits!}
-}

{-

uprfOfDisplay : (as : RFor)(c : RClause) → UPrfOf as c → UPrfDisplay

uPrfDisplayFor : (as : RFor)(cl : RFor) → (UPrfOfFor as cl) → UPrfDisplayFor


resultProof : UPrfOfFinalRes

UPrfOfConfig : (as : RFor) → Config → Set
UPrfOfConfig as (config nus uns) = UPrfOfFor as nus × UPrfOfLits as uns


UPrfOfFinalRes : (as : RFor) → FinalRes → Set
UPrfOfFinalRes as (failure cf) = UPrfOfConfig as cf
UPrfOfFinalRes as (continue cf) = UPrfOfConfig as cf
UPrfOfFinalRes as success = UPrfOf as []  -- uprfOfDisplay


-}
