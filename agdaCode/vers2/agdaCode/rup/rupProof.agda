module rup.rupProof where

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

UPrfOfConfig : (as : RFor) → Config → Set
UPrfOfConfig as (config nus uns) = UPrfOfFor as nus × UPrfOfLits as uns

UPrfOfIntermediateOneStepRes : (as : RFor) →  IntermediateOneStepRes
                                  → Set
UPrfOfIntermediateOneStepRes as (continue x) = UPrfOfConfig as x
UPrfOfIntermediateOneStepRes as success = UPrfOf as []

UPrfOfFinalRes : (as : RFor) → FinalRes → Set
UPrfOfFinalRes as (failure cf) = UPrfOfConfig as cf
UPrfOfFinalRes as (continue cf) = UPrfOfConfig as cf
UPrfOfFinalRes as success = UPrfOf as []

UPrfOfOneStepOneRClauseRes : (as : RFor) → OneStepOneRClauseRes → Set
UPrfOfOneStepOneRClauseRes as (continuec c) = UPrfOf as c
UPrfOfOneStepOneRClauseRes as (continuel l) = UPrfOfLit as l
UPrfOfOneStepOneRClauseRes as omit = ⊤
UPrfOfOneStepOneRClauseRes as success = UPrfOf as []


UPrfOfInitialConfig : (as : RFor) → InitialConfig → Set
UPrfOfInitialConfig as success = UPrfOf as []
UPrfOfInitialConfig as (continue cf) = UPrfOfConfig as cf

mutual
 urPrfOneStepOneRClausePropagate : (as : RFor)
                                    (c : RClause)(l : RLit)
                                    (pc : UPrfOf as c)
                                    (pl : UPrfOfLit as l)
                                    → UPrfOfOneStepOneRClauseRes as
                                       (oneStepOneRClausePropagate c l)
 urPrfOneStepOneRClausePropagate as  c l pc pl = urPrfOneStepOneRClausePropagateCheckIn as c l (l ∈b c) refl pc pl



 urPrfOneStepOneRClausePropagateCheckIn : (as : RFor)
                                          (cl : RClause)(l : RLit)
                                          (b : Bool)
                                          (bp : (l ∈b cl) ≡ b)
                                          (pc : UPrfOf as cl)
                                          (pl : UPrfOfLit as l)
                                          → UPrfOfOneStepOneRClauseRes as
                                       (oneStepOneRClausePropagateCheckIn cl l b)
 urPrfOneStepOneRClausePropagateCheckIn as cl l false bp pc pl rewrite bp
       = urPrfOneStepOneRClausePropagateCheckNotIn as cl l ((negRLit l) ∈b cl ) refl pc pl
 urPrfOneStepOneRClausePropagateCheckIn as cl l true bp pc pl = tt


 urPrfOneStepOneRClausePropagateCheckNotIn : (as : RFor)
                                          (c : RClause)(l : RLit)
                                          (b : Bool)
                                          (bp : ((negRLit l) ∈b c)  ≡ b)
                                          (pc : UPrfOf as c)
                                          (pl : UPrfOfLit as l)
                                          → UPrfOfOneStepOneRClauseRes as
                                       (oneStepOneRClausePropagateCheckNotIn c l b)
 urPrfOneStepOneRClausePropagateCheckNotIn as [] l false bp pc pl = tt
 urPrfOneStepOneRClausePropagateCheckNotIn as (x ∷ []) l false bp pc pl = pc
 urPrfOneStepOneRClausePropagateCheckNotIn as (x ∷ y ∷ c) l false bp pc pl = pc
 urPrfOneStepOneRClausePropagateCheckNotIn as (x ∷ []) l true bp pc pl =
   urPrfOneStepOneRClausePropagateRClauseCreated as ((x ∷ []) \\ (negRLit l)) (urPrfOfRes as (x ∷ []) l pc pl )
 urPrfOneStepOneRClausePropagateCheckNotIn as (x ∷ x₁ ∷ c) l true bp pc pl = urPrfOneStepOneRClausePropagateRClauseCreated as ((x ∷ x₁ ∷ c) \\ (negRLit l)) (urPrfOfRes as (x ∷ x₁ ∷ c) l pc pl )



 urPrfOneStepOneRClausePropagateRClauseCreated : (as : RFor)
                                          (c : RClause)
                                          (pc : UPrfOf as c)
                                          → UPrfOfOneStepOneRClauseRes as
                                       (oneStepOneRClausePropagateRClauseCreated c)
 urPrfOneStepOneRClausePropagateRClauseCreated as [] pc = pc
 urPrfOneStepOneRClausePropagateRClauseCreated as (c ∷ []) pc = pc
 urPrfOneStepOneRClausePropagateRClauseCreated as (c ∷ c₁ ∷ cl) pc = pc


mutual
 urPrfoneStepOneConfigPropagateIntermediate :
        (as : RFor)(cf : Config)(l : RLit)
        (asp : UPrfOfConfig as cf)
        (lp : UPrfOfLit as l)
        → UPrfOfIntermediateOneStepRes as
           (oneStepOneConfigPropagateIntermediate cf l)
 urPrfoneStepOneConfigPropagateIntermediate as (config (c ∷ cl) ls) l (π (π cp clp) lsp) lp
  = urPrfoneStepOneConfigPropagateOneRClause as c l
     (oneStepOneConfigPropagateIntermediate (config cl ls) l)
     cp lp (urPrfoneStepOneConfigPropagateIntermediate as (config cl ls) l
            (π clp lsp)  lp)

 urPrfoneStepOneConfigPropagateIntermediate as (config [] (l' ∷ ls)) l (π tt (π l'p lsp)) lp
   = urPrfoneStepOneConfigPropagateOneRClause as (l' ∷ []) l
     (oneStepOneConfigPropagateIntermediate (config [] ls) l)
     l'p lp
     (urPrfoneStepOneConfigPropagateIntermediate as (config [] ls) l
        (π tt lsp)  lp)
 urPrfoneStepOneConfigPropagateIntermediate as (config [] []) l asp lp = π tt tt


 urPrfoneStepOneConfigPropagateOneRClause :
   (as : RFor)(c : RClause)(l : RLit)(ih : IntermediateOneStepRes)
   (cp : UPrfOf as c) (lp : UPrfOfLit as l)
   (ihp : UPrfOfIntermediateOneStepRes as ih)
   →  UPrfOfIntermediateOneStepRes as
           (oneStepOneConfigPropagateOneRClause c l ih)
 urPrfoneStepOneConfigPropagateOneRClause as c l (continue cf) cp lp ihp
    = urPrfoneStepOneConfigPropagateOneRClauseStep2 as cf
        (oneStepOneRClausePropagate c l) ihp
         (urPrfOneStepOneRClausePropagate as c l cp lp)
 urPrfoneStepOneConfigPropagateOneRClause as c l success cp lp ihp = ihp

 urPrfoneStepOneConfigPropagateOneRClauseStep2 :
   (as : RFor)(cf : Config) (oneStepRes : OneStepOneRClauseRes)
   (cfp : UPrfOfConfig as cf)
   (oneStepResp : UPrfOfOneStepOneRClauseRes as oneStepRes)
   → UPrfOfIntermediateOneStepRes as
      (oneStepOneConfigPropagateOneRClauseStep2 cf oneStepRes)
 urPrfoneStepOneConfigPropagateOneRClauseStep2 as (config nunitCl unitCl) (continuec c₁) (π nunp unp) oneStepResp
   = π (π  oneStepResp nunp ) unp
 urPrfoneStepOneConfigPropagateOneRClauseStep2 as cf (continuel l') (π cfp mcf) oneStepResp = π cfp (π oneStepResp mcf )
 urPrfoneStepOneConfigPropagateOneRClauseStep2 as cf omit cfp oneStepResp = cfp
 urPrfoneStepOneConfigPropagateOneRClauseStep2 as cf success cfp oneStepResp = oneStepResp


prfIntermediateOneStep2FinalStep
  : (as : RFor) (i : IntermediateOneStepRes)
    (ip : UPrfOfIntermediateOneStepRes as i)
    → UPrfOfFinalRes as (intermediateOneStep2FinalStep i)
prfIntermediateOneStep2FinalStep as (continue (config nunitCl [])) (π nunitClp tt) = π nunitClp tt
prfIntermediateOneStep2FinalStep as (continue (config nunitCl (x ∷ unitCl))) ip = ip
prfIntermediateOneStep2FinalStep as success ip = ip

prfoneStepOneConfigPropagateFinal
   : (as : RFor)(cf : Config)(cfp : UPrfOfConfig as cf)
     → UPrfOfFinalRes as (oneStepOneConfigPropagateFinal cf)
prfoneStepOneConfigPropagateFinal as (config nunitCl []) (π nunitClp tt)
   = π nunitClp tt
prfoneStepOneConfigPropagateFinal as (config nunitCl (l ∷ ls)) (π nunitClp (π lp lsp))
    = prfIntermediateOneStep2FinalStep as
      (oneStepOneConfigPropagateIntermediate (config nunitCl ls) l)
      (urPrfoneStepOneConfigPropagateIntermediate as (config nunitCl ls)
         l (π nunitClp lsp) lp)


mutual
  prfnStepsConfigPropagateFinal
     : (as : RFor)(cf : Config)(n :  ℕ)
       (cfp : UPrfOfConfig as cf)
       → UPrfOfFinalRes as (nStepsConfigPropagateFinal cf n)
  prfnStepsConfigPropagateFinal as (config nunitCl unitCl) zero cfp = cfp
  prfnStepsConfigPropagateFinal as cf (suc n) cfp =
        prfnStepsConfigPropagateFinalaux as
          (oneStepOneConfigPropagateFinal cf) n
          (prfoneStepOneConfigPropagateFinal as cf cfp)
        --

  prfnStepsConfigPropagateFinalaux
   : (as : RFor)(f : FinalRes)(n : ℕ)
     (fp : UPrfOfFinalRes as f)
     → UPrfOfFinalRes as (nStepsConfigPropagateFinalaux f n)
  prfnStepsConfigPropagateFinalaux as (failure c) n fp = fp
  prfnStepsConfigPropagateFinalaux as (continue (config nu un)) n (π nup unp) = prfnStepsConfigPropagateFinal as (config nu un) n (π nup unp)
  prfnStepsConfigPropagateFinalaux as success n fp = fp


mutual
  prfInitialConfig : (as : RFor)
                     (cl : RFor)
                     (pcl : UPrfOfFor as cl)
                     → UPrfOfInitialConfig as (initialConfig cl)
  prfInitialConfig as [] pcl = π tt tt
  prfInitialConfig as (c ∷ cl) (π cp clp)
     = prfinitialConfigAux as c (initialConfig cl) cp
       (prfInitialConfig as cl clp)

  prfinitialConfigAux
     : (as : RFor)(c : RClause)
       (i : InitialConfig)
       (cp : UPrfOf as c)
       (ip : UPrfOfInitialConfig as i)
       → UPrfOfInitialConfig as (initialConfigAux c i)
  prfinitialConfigAux as [] i cp ip = cp
  prfinitialConfigAux as (l ∷ c) success cp ip = ip
  prfinitialConfigAux as (l ∷ []) (continue (config nCl uCl)) cp (π nClp uClp) = π nClp (π cp uClp)
  prfinitialConfigAux as (l ∷ x ∷ c) (continue (config nCl uCl))
     (uPrfOf asp aspCor) (π nClp uClp)
     = π (π (uPrfOf asp aspCor) nClp) uClp


prfnStepsInitialConfigPropagateFinal
   : (as : RFor) (i : InitialConfig)(n : ℕ)(pi : UPrfOfInitialConfig as i)
     → UPrfOfFinalRes as (nStepsInitialConfigPropagateFinal i n)
prfnStepsInitialConfigPropagateFinal as success n pi = pi
prfnStepsInitialConfigPropagateFinal as (continue cl) n pi
         = prfnStepsConfigPropagateFinal as cl n pi

prfChecOneRupWithInfo
   : (as : RFor)(rp : RClause)
     → UPrfOfFinalRes (createFullRupRClause as rp) (checkOneRupWithInfo as rp)
prfChecOneRupWithInfo as rp =
    let
      cl' : RFor
      cl' = createFullRupRClause as rp

      n : ℕ
      n = #varsInRClauses cl'

      inConfig : InitialConfig
      inConfig = initialConfig cl'

      cl'p : UPrfOfFor cl' cl'
      cl'p = assUPrf cl'

      inConfigp : UPrfOfInitialConfig cl' inConfig
      inConfigp = prfInitialConfig cl' cl' cl'p

    in prfnStepsInitialConfigPropagateFinal cl' inConfig n inConfigp


finalResPrf2Prf : (as : RFor)(p : FinalRes)(cor : atom (finalRes2Bool p))
                  (q : UPrfOfFinalRes as p)
                  → UPrfOf as []
finalResPrf2Prf as success cor q = q

prfcheckOneRup : (f : RFor)(rp : RClause) → (atom (checkOneRup f rp))
                 → UPrfOf  (createFullRupRClause f rp) []
prfcheckOneRup f rp cor
   = finalResPrf2Prf (createFullRupRClause f rp)
     (checkOneRupWithInfo f rp) cor (prfChecOneRupWithInfo f rp)


unSatCheckOneRup : (f : RFor)(rp : RClause) → (atom (checkOneRup f rp)) →
                   EntailsRCl (createFullRupRClause f rp) []
unSatCheckOneRup f rp cor mod v =
    let
        as  : RFor
        as   = createFullRupRClause f rp

        prf : UPrfOf  as []
        prf = prfcheckOneRup f rp cor
    in uPrfOfEntails as [] prf mod v


rupCorrect : (f : RFor)(rp : RClause) → (atom (checkOneRup f rp))
             → EntailsRCl f rp

rupCorrect f rp cor
      = let
          p1 : EntailsRCl ((lits2RClauses (negRLits (reverseList rp))) ++ f) []
          p1 = unSatCheckOneRup f rp cor

          p2 : EntailsRCl f (rp ++ [])
          p2 = entailsMoveFromAs2ConclList f rp [] p1

          p3 : EntailsRCl f rp
          p3 = transfer≡hid (λ y → EntailsRCl f y) (++empty rp) p2

        in p3



rupProofEntails : (f : RFor)(p : RupProof)
                  → atom (rupProof f p)
                  → EntailsRFor f p
rupProofEntails f [] q mod p = tt
rupProofEntails f (rp ∷ rs) q mod p'
     = let
          p1 : atom (checkOneRup f rp)
          p1 = ∧b-elim1  (checkOneRup f rp) (rupProof (rp ∷ f) rs) q

          p2 : atom (rupProof (rp ∷ f) rs)
          p2 = ∧b-elim2  (checkOneRup f rp) (rupProof (rp ∷ f) rs) q

          q : EvalRClause mod rp
          q = rupCorrect f rp p1 mod p'

          r : EvalRFor mod (rp ∷ f)
          r = π q p'

          q2 : EvalRFor mod rs
          q2 = rupProofEntails (rp ∷ f) rs p2 mod r

       in π q q2

rupProofOfUnsatUnsat : (f : RFor)(p : RupProof)
                       → atom (rupProofOfUnSat f p)
                       → UnSatFor f
rupProofOfUnsatUnsat f r q =
   let
       q' : atom (rupProof f r)
       q' = ∧b-elim1 (rupProof f r) ([] ∈b r) q

       q'' : [] ∈ r
       q'' = ∧b-elim2 (rupProof f r) ([] ∈b r) q

       q3 : EntailsRFor f r
       q3 = rupProofEntails f r q'

   in RForWith[]NotEntailed f r q'' q3
