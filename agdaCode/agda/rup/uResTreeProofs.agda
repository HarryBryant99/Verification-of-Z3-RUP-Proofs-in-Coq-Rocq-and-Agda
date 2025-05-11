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
  data UPrf (as : Formula) : Set where
    ass : Fin (length as) → UPrf as
    res : (t1 t2 : UPrf as)(l : Literal)
          (ur : conclusionUR as t2 ≡ (l ∷ []))
          → UPrf as

  conclusionUR : (as : Formula) → UPrf as → Clause
  conclusionUR as (ass i) = nthFin as i
  conclusionUR as (res p p₁ l ur) =  (conclusionUR as  p) \\ (negL l)


IsAssUPrf : (as : Formula) (p : UPrf as) → Set
IsAssUPrf as (ass x) = ⊤
IsAssUPrf as (res p p₁ l ur) = ⊥

uPrfEntails : (as : Formula)(p : UPrf as)
              → EntailsCl as (conclusionUR as p)
uPrfEntails as (ass i) mod asT = nthClauseImpliesListClause mod as i asT
uPrfEntails as (res p p₁ l ur) mod asT =
    let
        pentails : EvalClause mod (conclusionUR as p)
        pentails = uPrfEntails as p mod asT

        p₁entails : EvalClause mod (conclusionUR as p₁)
        p₁entails = uPrfEntails as p₁ mod asT

        lTrue : EvalClause mod (l ∷ [])
        lTrue = transfer≡  (λ c → EvalClause mod c) (conclusionUR as p₁) (l ∷ []) ur p₁entails


        lTrue' : EvalLit mod l
        lTrue' = evalUnitClauseToUnit mod l lTrue

    in evalMod' mod l (conclusionUR as p) lTrue' pentails


record UPrfOf (as : Formula)(c : Clause) : Set where
  constructor uPrfOf
  field
    prf     : UPrf as
    corPrf  : conclusionUR as prf ≡ c
open UPrfOf public


IsAssUrproofOf : (as : Formula) (c : Clause)(p : UPrfOf as c) → Set
IsAssUrproofOf as c (uPrfOf prf₁ corPrf₁) = IsAssUPrf as prf₁


UPrfOfLit : (as : Formula)(l : Literal) →  Set
UPrfOfLit as l = UPrfOf as (l ∷ [])

uPrfOfEntails : (as : Formula)(c : Clause)(p : UPrfOf as c)
                → EntailsCl as c
uPrfOfEntails as c (uPrfOf pr corPr) mod asT =
     let
         conc : Clause
         conc = conclusionUR as pr

         entailed : EvalClause mod conc
         entailed = uPrfEntails as pr mod asT

     in transfer≡ (EvalClause mod) conc c corPr entailed


IsAssUrproofOfLit : (as : Formula) (l : Literal)(p : UPrfOfLit as l) → Set
IsAssUrproofOfLit as l p = IsAssUrproofOf as (l ∷ [])  p


conclusionURlist : (as : Formula)(ls : List (UPrf as)) → Formula
conclusionURlist as [] = []
conclusionURlist as (x ∷ ls) = conclusionUR as x ∷ conclusionURlist as ls

conclusionURvec : (as : Formula){n : ℕ}(ls : Vec (UPrf as) n) → Vec Clause n
conclusionURvec as [] = []
conclusionURvec as (x ∷ ls) = conclusionUR as x ∷ conclusionURvec as ls

UPrfOfFor : (as : Formula)(cl : Formula) → Set
UPrfOfFor as [] = ⊤
UPrfOfFor as (c ∷ cl) = UPrfOf as c × UPrfOfFor as cl

UPrfOfLits : (as : Formula)(ls : List Literal) → Set
UPrfOfLits as ls = UPrfOfFor as (lits2Clauses ls)

IsAssUprfOfList : (as : Formula)(cl : Formula)(p : UPrfOfFor as cl)
                     → Set
IsAssUprfOfList as [] p = ⊤
IsAssUprfOfList as (c ∷ cl) (π pc pcl) = IsAssUrproofOf as c pc ×
                                            IsAssUprfOfList as cl pcl

IsAssuPrfOfLits : (as : Formula)(ls : List Literal)(p : UPrfOfLits as ls)
                     → Set
IsAssuPrfOfLits as ls p = IsAssUprfOfList as (lits2Clauses ls) p

uPrfOfForEntails : (as : Formula)(cl : Formula)
                   (p : UPrfOfFor as cl)
                   → EntailsFor as cl
uPrfOfForEntails as [] tt mod asT = tt
uPrfOfForEntails as (c ∷ cl) (π pc pcl) mod asT = π (uPrfOfEntails as c pc mod asT) (uPrfOfForEntails as cl pcl mod asT)



liftAss : (c : Clause)(as : Formula)(c₁ : Clause)(p : UPrfOf as c₁)
          → IsAssUrproofOf as c₁ p
          → UPrfOf (c ∷ as) c₁
liftAss c as c₁ (uPrfOf (ass x) corPrf₁) q = uPrfOf (ass (suc x)) corPrf₁

liftAssIsAss : (c : Clause)(as : Formula)(c₁ : Clause)
               (p : UPrfOf as c₁)(isas : IsAssUrproofOf as c₁ p)
           → IsAssUrproofOf (c ∷ as) c₁ (liftAss c as c₁ p isas)
liftAssIsAss c as c₁ (uPrfOf (ass x) corPrf₁) isas = tt


liftAssList : (c : Clause)(as : Formula)(cl : Formula)
              (p : UPrfOfFor as cl)
              (q : IsAssUprfOfList as cl p)
          → UPrfOfFor (c ∷ as) cl
liftAssList c as [] p q = tt
liftAssList c as (x ∷ cl) (π prx prcl) (π prxass prclass ) = π (liftAss c as x prx prxass ) (liftAssList c as cl prcl prclass)

liftAssListIsAss : (c : Clause)(as : Formula)(cl : Formula)
              (p : UPrfOfFor as cl)
              (q : IsAssUprfOfList as cl p)
              → IsAssUprfOfList (c ∷ as) cl (liftAssList c as cl p q)
liftAssListIsAss c as [] p q = tt
liftAssListIsAss c as (x ∷ cl) (π xpr clpr) (π xprass clprass)
       = π (liftAssIsAss c as x xpr xprass)
           (liftAssListIsAss c as cl clpr clprass)


assUPrf1 : (as : Formula) → List (UPrf as)
assUPrf1 as = funToList ass

mutual
  assUPrf : (as : Formula) → UPrfOfFor as as
  assUPrf [] = tt
  assUPrf (c ∷ as) = π (uPrfOf (ass zero) refl)
                        (liftAssList c as as (assUPrf as) (assUPrfIsAssProof as) )

  assUPrfIsAssProof : (as : Formula)
                         → IsAssUprfOfList as as (assUPrf as)
  assUPrfIsAssProof [] = tt
  assUPrfIsAssProof (x ∷ as) = π tt
                                   (liftAssListIsAss x as as (assUPrf as) (assUPrfIsAssProof as))


urPrfOfRes : (as : Formula)(c : Clause)(l : Literal)
             (pc : UPrfOf as c)(pl : UPrfOfLit as l)
             → UPrfOf as (c \\ negL l)
urPrfOfRes as c l (uPrfOf prf₁ corPrf₁)
                  (uPrfOf prf₂ corPrf₂)
     = uPrfOf (res prf₁ prf₂ l corPrf₂) (cong≡ (λ x → x \\ negL l) corPrf₁ )
