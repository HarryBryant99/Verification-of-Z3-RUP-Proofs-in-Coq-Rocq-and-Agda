module rup.z3Model where

open import Data.String

open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny
open import lib.stringLib
open import lib.emptyLib


open import rup.z3Variables
open import rup.z3Formulas
open import rup.model
open import rup.clause
open import rup.variablesBasedOnZ3formulas
open import rup.z3BasedClause

ZModel : Set
ZModel = ZVar → Bool

evalZVar : ZModel → ZVar → Bool
evalZVar mod v = mod v

EvalZVar : ZModel → ZVar → Set
EvalZVar mod v = atom (evalZVar mod v)


mutual
  evalZFor : ZModel → ZFor → Bool
  evalZFor mod (zvar f) = evalZVar mod f
  evalZFor mod (andFor l) = andListBool (evalListZFor mod  l)
  evalZFor mod (orFor l) = orListBool (evalListZFor mod l)
  evalZFor mod (impFor f g) = evalZFor mod f ->b evalZFor mod g
  evalZFor mod (notFor f) = not (evalZFor mod f)
  evalZFor mod trueFor = true
  evalZFor mod falseFor = false

  evalListZFor : ZModel → List ZFor → List Bool
  evalListZFor mod [] = []
  evalListZFor mod (f ∷ l) = evalZFor mod f ∷ evalListZFor mod l

evalZClause : ZModel → ZClause → Bool
evalZClause mod l = orListBool (evalListZFor mod l)

EvalZClause : ZModel → ZClause → Set
EvalZClause mod l = atom (evalZClause mod l)

evalListZClause : ZModel → List ZClause → Bool
evalListZClause mod l = andListBool (mapList (evalZClause mod) l)

EvalListZClause : ZModel → List ZClause → Set
EvalListZClause mod l = atom (evalListZClause mod l)



zModel2Rmodel : ZModel → RModel
zModel2Rmodel = evalZFor

rLitZModel≡ : (mod : ZModel)(f : ZFor)
               → evalZFor mod f ≡ evalRLit (zModel2Rmodel mod) (Zfor2Lit f)
rLitZModel≡ mod (notFor f) rewrite (negRLitEval₁' (zModel2Rmodel mod) (Zfor2Lit f))
             = cong≡ not (rLitZModel≡ mod f)
rLitZModel≡ mod (zvar x) = refl
rLitZModel≡ mod (andFor l) = refl
rLitZModel≡ mod (orFor l) = refl
rLitZModel≡ mod (impFor f g) = refl
rLitZModel≡ mod trueFor = refl
rLitZModel≡ mod falseFor = refl


rClauseZModel≡ : (mod : ZModel)(c : ZClause)
               → evalZClause mod c ≡ evalRClause (zModel2Rmodel mod) (zCl2RClause c)
rClauseZModel≡ mod [] = refl
rClauseZModel≡ mod (x ∷ c) = orEq (evalZFor mod x) (evalRLit (evalZFor mod) (Zfor2Lit x)) (orListBool (evalListZFor mod c)) (orListBool (mapList (evalRLit (evalZFor mod)) (zCl2RClause c)))
                             (rLitZModel≡ mod x) (rClauseZModel≡ mod c)

rClauseZModel-> : (mod : ZModel)(c : ZClause)
               → EvalZClause mod c →  EvalRClause (zModel2Rmodel mod) (zCl2RClause c)
rClauseZModel-> mod c p rewrite (rClauseZModel≡ mod c) = p

rClauseZModel->' : (mod : ZModel)(c : ZClause)
               →  EvalRClause (zModel2Rmodel mod) (zCl2RClause c) → EvalZClause mod c
rClauseZModel->' mod c p rewrite (rClauseZModel≡ mod c) = p




rListClZModel≡ : (mod : ZModel)(cl : List ZClause)
               → evalListZClause mod cl ≡ evalRFor (zModel2Rmodel mod) (zListCl2RListCl cl)
rListClZModel≡ mod [] = refl
rListClZModel≡ mod (c ∷ cl) = andEq (orListBool (evalListZFor mod c)) (orListBool (mapList (evalRLit (evalZFor mod)) (zCl2RClause c)))
                                    (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) cl)) (andListBool
                                    (mapList (λ l → orListBool (mapList (evalRLit (evalZFor mod)) l))
                                    (zListCl2RListCl cl)))
                                    (rClauseZModel≡ mod c ) (rListClZModel≡ mod cl)


rListClZModel-> : (mod : ZModel)(cl : List ZClause)
               → EvalListZClause mod cl → EvalRFor (zModel2Rmodel mod) (zListCl2RListCl cl)
rListClZModel-> mod cl p rewrite (rListClZModel≡ mod cl) = EvalRFor'2For (evalZFor mod) (zListCl2RListCl cl) p

EntailsListZCl : (as : List ZClause)(f : List ZClause) → Set
EntailsListZCl as f = (mod : ZModel) → EvalListZClause mod as → EvalListZClause mod f

EntailsZCl : (as : List ZClause)(c : ZClause) → Set
EntailsZCl as c = (mod : ZModel) → EvalListZClause mod as → EvalZClause mod c


entailsRCl2ZCl : (as : List ZClause)(c : ZClause) → EntailsRCl (zListCl2RListCl as) (zCl2RClause c)
                     → EntailsZCl as c
entailsRCl2ZCl as c  ent mod p =
    let
       p' : EvalRFor (zModel2Rmodel mod) (zListCl2RListCl as)
       p' = rListClZModel-> mod as p

       q : EvalRClause (zModel2Rmodel mod) (zCl2RClause c)
       q = ent (zModel2Rmodel mod) p'
    in rClauseZModel->' mod c q


entailsListCladd1 : (as cl : List ZClause)(c : ZClause)
         → EntailsListZCl as cl
         → EntailsZCl as c
         → EntailsListZCl as (c ∷ cl)
entailsListCladd1 as cl c ascl asc mod asev = ∧b-intro (orListBool (evalListZFor mod c))
                                                (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) cl))
                                                (asc mod asev) (ascl mod asev)


entailsZCladdInference' : (as cl : List ZClause)(c : ZClause)
                        → EntailsListZCl as cl
                        → EntailsZCl cl c
                        → EntailsZCl as c
entailsZCladdInference' as cl c ascl clc mod asev =
      let
          p : EvalListZClause mod cl
          p = ascl mod asev
      in clc mod p


entailsZCladdInference : (as cl : List ZClause)(c : ZClause)
                        → EntailsListZCl as cl
                        → EntailsZCl cl c
                        → EntailsListZCl as (c ∷ cl)
entailsZCladdInference as cl c ascl clc = entailsListCladd1 as cl c ascl (entailsZCladdInference' as cl c ascl clc)


entailsAddAss : (as cl : List ZClause)(c : ZClause)
                → EntailsListZCl as cl
                → EntailsListZCl (c ∷ as) (c ∷ cl)
entailsAddAss as cl c ascl mod casp = ∧b-intro (orListBool (evalListZFor mod c))
                                        (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) cl))
                                        (∧b-elim1 (orListBool (evalListZFor mod c))
                                           (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) as))
                                           casp)
                                        (ascl mod ((∧b-elim2 (orListBool (evalListZFor mod c))
                                           (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) as))
                                           casp)))


ZTaut : (c : ZClause) → Set
ZTaut c = (mod : ZModel) → EvalZClause mod c

entailsAddTaut' : (c : ZClause)
                  → ZTaut c
                  → (as : List ZClause)
                  → EntailsZCl as c
entailsAddTaut' c ctaut _ mod _ = ctaut mod


entailsAddTaut  : (c : ZClause)
                  → ZTaut c
                  → (as cl : List ZClause)
                  → EntailsListZCl as cl
                  → EntailsListZCl as (c ∷ cl)
entailsAddTaut  c ctaut as cl ascl mod asev = ∧b-intro (orListBool (evalListZFor mod c))
                                                (andListBool (mapList (λ l → orListBool (evalListZFor mod l)) cl))
                                                (ctaut mod) (ascl mod asev)


containsEmptyUnSat' : (l : List (List ZFor))→ (ContainsEmpty  l)  → (mod : ZModel) → EvalListZClause mod l → ⊥
containsEmptyUnSat' ((f ∷ c) ∷ l) p mod  q =
     containsEmptyUnSat' l p mod
    (∧b-elim2 (evalZFor mod f ∨b orListBool (evalListZFor mod c))
             (andListBool (mapList (λ l₂ → orListBool (evalListZFor mod l₂)) l))  q)


UnSat : (l : List (List ZFor)) → Set
UnSat l = (mod : ZModel) → EvalListZClause mod l → ⊥

containsEmptyUnSat : (l : List (List ZFor)) → (ContainsEmpty  l)  → UnSat l
containsEmptyUnSat = containsEmptyUnSat'


entailsUnSatUnSat : (l l' : List (List ZFor))
                    → EntailsListZCl l l'
                    → UnSat l'
                    → UnSat l
entailsUnSatUnSat l l' ll' ¬l' mod lmod = ¬l' mod (ll' mod lmod)
