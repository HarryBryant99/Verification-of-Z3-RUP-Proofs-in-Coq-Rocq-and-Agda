module rup.uResTreeProofs where

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

mutual
  data UPrf (as : RFor) : Set where
    ass : Fin (length as) → UPrf as
    res : (t1 t2 : UPrf as)(l : RLit)
          (ur : conclusionUR as t2 ≡ (l ∷ []))
          → UPrf as

  conclusionUR : (as : RFor) → UPrf as → RClause
  conclusionUR as (ass i) = nthFin as i
  conclusionUR as (res p p₁ l ur) =  (conclusionUR as  p) \\ (negRLit l)


IsAssUPrf : (as : RFor) (p : UPrf as) → Set
IsAssUPrf as (ass x) = ⊤
IsAssUPrf as (res p p₁ l ur) = ⊥

uPrfEntails : (as : RFor)(p : UPrf as)
              → EntailsRCl as (conclusionUR as p)
uPrfEntails as (ass i) mod asT = nthRClauseImpliesListRClause mod as i asT
uPrfEntails as (res p p₁ l ur) mod asT =
    let
        pentails : EvalRClause mod (conclusionUR as p)
        pentails = uPrfEntails as p mod asT

        p₁entails : EvalRClause mod (conclusionUR as p₁)
        p₁entails = uPrfEntails as p₁ mod asT

        lTrue : EvalRClause mod (l ∷ [])
        lTrue = transfer≡  (λ c → EvalRClause mod c) (conclusionUR as p₁) (l ∷ []) ur p₁entails


        lTrue' : EvalLit mod l
        lTrue' = evalUnitRClauseToUnit mod l lTrue

    in evalMod' mod l (conclusionUR as p) lTrue' pentails


record UPrfOf (as : RFor)(c : RClause) : Set where
  constructor uPrfOf
  field
    prf     : UPrf as
    corPrf  : conclusionUR as prf ≡ c
open UPrfOf public


IsAssUrproofOf : (as : RFor) (c : RClause)(p : UPrfOf as c) → Set
IsAssUrproofOf as c (uPrfOf prf₁ corPrf₁) = IsAssUPrf as prf₁


UPrfOfLit : (as : RFor)(l : RLit) →  Set
UPrfOfLit as l = UPrfOf as (l ∷ [])

uPrfOfEntails : (as : RFor)(c : RClause)(p : UPrfOf as c)
                → EntailsRCl as c
uPrfOfEntails as c (uPrfOf pr corPr) mod asT =
     let
         conc : RClause
         conc = conclusionUR as pr

         entailed : EvalRClause mod conc
         entailed = uPrfEntails as pr mod asT

     in transfer≡ (EvalRClause mod) conc c corPr entailed


IsAssUrproofOfLit : (as : RFor) (l : RLit)(p : UPrfOfLit as l) → Set
IsAssUrproofOfLit as l p = IsAssUrproofOf as (l ∷ [])  p


conclusionURlist : (as : RFor)(ls : List (UPrf as)) → RFor
conclusionURlist as [] = []
conclusionURlist as (x ∷ ls) = conclusionUR as x ∷ conclusionURlist as ls

conclusionURvec : (as : RFor){n : ℕ}(ls : Vec (UPrf as) n) → Vec RClause n
conclusionURvec as [] = []
conclusionURvec as (x ∷ ls) = conclusionUR as x ∷ conclusionURvec as ls

UPrfOfFor : (as : RFor)(cl : RFor) → Set
UPrfOfFor as [] = ⊤
UPrfOfFor as (c ∷ cl) = UPrfOf as c × UPrfOfFor as cl

UPrfOfLits : (as : RFor)(ls : List RLit) → Set
UPrfOfLits as ls = UPrfOfFor as (lits2RClauses ls)

IsAssUprfOfList : (as : RFor)(cl : RFor)(p : UPrfOfFor as cl)
                     → Set
IsAssUprfOfList as [] p = ⊤
IsAssUprfOfList as (c ∷ cl) (π pc pcl) = IsAssUrproofOf as c pc ×
                                            IsAssUprfOfList as cl pcl

IsAssuPrfOfLits : (as : RFor)(ls : List RLit)(p : UPrfOfLits as ls)
                     → Set
IsAssuPrfOfLits as ls p = IsAssUprfOfList as (lits2RClauses ls) p

uPrfOfForEntails : (as : RFor)(cl : RFor)
                   (p : UPrfOfFor as cl)
                   → EntailsRFor as cl
uPrfOfForEntails as [] tt mod asT = tt
uPrfOfForEntails as (c ∷ cl) (π pc pcl) mod asT = π (uPrfOfEntails as c pc mod asT) (uPrfOfForEntails as cl pcl mod asT)



liftAss : (c : RClause)(as : RFor)(c₁ : RClause)(p : UPrfOf as c₁)
          → IsAssUrproofOf as c₁ p
          → UPrfOf (c ∷ as) c₁
liftAss c as c₁ (uPrfOf (ass x) corPrf₁) q = uPrfOf (ass (suc x)) corPrf₁

liftAssIsAss : (c : RClause)(as : RFor)(c₁ : RClause)
               (p : UPrfOf as c₁)(isas : IsAssUrproofOf as c₁ p)
           → IsAssUrproofOf (c ∷ as) c₁ (liftAss c as c₁ p isas)
liftAssIsAss c as c₁ (uPrfOf (ass x) corPrf₁) isas = tt


liftAssList : (c : RClause)(as : RFor)(cl : RFor)
              (p : UPrfOfFor as cl)
              (q : IsAssUprfOfList as cl p)
          → UPrfOfFor (c ∷ as) cl
liftAssList c as [] p q = tt
liftAssList c as (x ∷ cl) (π prx prcl) (π prxass prclass ) = π (liftAss c as x prx prxass ) (liftAssList c as cl prcl prclass)

liftAssListIsAss : (c : RClause)(as : RFor)(cl : RFor)
              (p : UPrfOfFor as cl)
              (q : IsAssUprfOfList as cl p)
              → IsAssUprfOfList (c ∷ as) cl (liftAssList c as cl p q)
liftAssListIsAss c as [] p q = tt
liftAssListIsAss c as (x ∷ cl) (π xpr clpr) (π xprass clprass)
       = π (liftAssIsAss c as x xpr xprass)
           (liftAssListIsAss c as cl clpr clprass)


assUPrf1 : (as : RFor) → List (UPrf as)
assUPrf1 as = funToList ass

mutual
  assUPrf : (as : RFor) → UPrfOfFor as as
  assUPrf [] = tt
  assUPrf (c ∷ as) = π (uPrfOf (ass zero) refl)
                        (liftAssList c as as (assUPrf as) (assUPrfIsAssProof as) )

  assUPrfIsAssProof : (as : RFor)
                         → IsAssUprfOfList as as (assUPrf as)
  assUPrfIsAssProof [] = tt
  assUPrfIsAssProof (x ∷ as) = π tt
                                   (liftAssListIsAss x as as (assUPrf as) (assUPrfIsAssProof as))


urPrfOfRes : (as : RFor)(c : RClause)(l : RLit)
             (pc : UPrfOf as c)(pl : UPrfOfLit as l)
             → UPrfOf as (c \\ negRLit l)
urPrfOfRes as c l (uPrfOf prf₁ corPrf₁)
                  (uPrfOf prf₂ corPrf₂)
     = uPrfOf (res prf₁ prf₂ l corPrf₂) (cong≡ (λ x → x \\ negRLit l) corPrf₁ )
