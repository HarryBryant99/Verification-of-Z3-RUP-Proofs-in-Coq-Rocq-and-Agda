module rup.model where

open import lib.boolLib
open import lib.emptyLib
open import lib.eqLib
open import lib.finLib
open import lib.listLib
open import lib.natLib
open import lib.prodLib
open import lib.sumLib
open import lib.unitLib
open import lib.vecLib

open import rup.variables
open import rup.clause


RModel : Set
RModel = RVar → Bool

evalRVar : RModel → RVar → Bool
evalRVar mod v = mod v

EvalRVar : RModel → RVar → Set
EvalRVar mod v = atom (evalRVar mod v)

evalRLit : RModel → RLit → Bool
evalRLit mod (pos v) = evalRVar mod v
evalRLit mod (neg v) = not (evalRVar mod v)

EvalLit : RModel → RLit → Set
EvalLit mod v = atom (evalRLit mod v)

evalRClause : RModel → RClause → Bool
evalRClause mod l = orListBool (mapList  (evalRLit mod) l)
-- evalRClause mod [] = false
-- evalRClause mod (l ∷ ls) = evalRLit mod l ∨b evalRClause mod ls

EvalRClause : RModel → RClause → Set
EvalRClause mod v = atom (evalRClause mod v)


evalUnitRClauseToUnit : (mod : RModel)(l : RLit)
                       → EvalRClause mod (l ∷ [])
                       → EvalLit mod l
evalUnitRClauseToUnit mod l p =
    let
       p' :  atom (evalRLit mod l) ⊎ atom false
       p' = orAtomTo⊎ (evalRLit mod l) false p
    in  or⊥₁ p'

evalRFor : RModel → RFor → Bool
evalRFor mod l = andListBool (mapList (evalRClause mod) l)

EvalRFor : RModel → RFor → Set
EvalRFor mod [] = ⊤
EvalRFor mod (l ∷ ls) = EvalRClause mod l × EvalRFor mod ls

EvalRFor' : RModel → RFor → Set
EvalRFor' mod l = atom (evalRFor mod l)

EvalRFor2For' : (mod : RModel)(f : RFor) → EvalRFor mod f → EvalRFor' mod f
EvalRFor2For' mod [] p = p
EvalRFor2For' mod (c ∷ cl) (π evc evl) = ∧b-intro (orListBool (mapList (evalRLit mod) c) ) (andListBool
       (mapList (λ l → orListBool (mapList (evalRLit mod) l)) cl))
        evc (EvalRFor2For' mod cl evl)


EvalRFor'2For : (mod : RModel)(f : RFor) → EvalRFor' mod f → EvalRFor mod f
EvalRFor'2For mod [] p = p
EvalRFor'2For mod (x ∷ f) p .fst = ∧b-elim1 (orListBool (mapList (evalRLit mod) x))
                                     (andListBool
                                      (mapList (λ l → orListBool (mapList (evalRLit mod) l)) f))
                                     p
EvalRFor'2For mod (x ∷ f) p .snd = EvalRFor'2For mod f
                                     (∧b-elim2 (orListBool (mapList (evalRLit mod) x))
                                               (andListBool
                                                (mapList (λ l → orListBool (mapList (evalRLit mod) l)) f))
                                     p)

{-
Goal: EvalRFor mod f
————————————————————————————————————————————————————————————
p   : T
      (orListBool (mapList (evalRLit mod) x) ∧b
       andListBool
       (mapList (λ l → orListBool (mapList (evalRLit mod) l)) f))
f   : List (List RLit)
x   : List RLit
mod : rup.z3Formulas.ZFor → Bool
-}



EmptyRClauseFalse : (mod : RModel) → IsFalse (evalRClause mod [])
EmptyRClauseFalse mod = tt

RModelsLorNegL : (mod : RModel) (l : RLit) → EvalLit mod l ⊎ EvalLit mod (negRLit l)
RModelsLorNegL mod (pos x) = tertiumNonD (mod x)
RModelsLorNegL mod (neg x) = tertiumNonD' (mod x)

ContradicLit : (mod : RModel) (l : RLit) → EvalLit mod l
               → EvalLit mod (negRLit l) → ⊥
ContradicLit mod (pos x) p p' = contradictBool (mod x) p p'
ContradicLit mod (neg x) p p' = contradictBool (mod x) p' p

LitImpliesNegNegL  : (mod :  RModel) (l : RLit)
                     → EvalLit mod l
                     → EvalLit mod (negRLit (negRLit l))
LitImpliesNegNegL mod (pos x) p = p
LitImpliesNegNegL mod (neg x) p = p


mutual
  evalMod : (mod : RModel) (l : RLit)(c : RClause)
            (lF : EvalLit mod (negRLit l))
            (cT : EvalRClause mod c)
            → EvalRClause mod (c \\ l)
  evalMod mod l (x ∷ c) lF cT = evalModaux1 mod l x c lF (orAtomTo⊎ (evalRLit mod x)(evalRClause mod c) cT)
  -- T (evalRClause mod (setminusAux x c l (l ==Lit x)))

  evalModaux1 : (mod : RModel) (l x : RLit)(c : RClause)
            (lF : EvalLit mod (negRLit l))
            (cT : EvalLit mod x ⊎ EvalRClause mod c)
            → EvalRClause mod (setminusAux x c l (l ==RLit x))
  evalModaux1 mod l x lF cT (inj₁ x₁) with (l ==RLit x) in eq
  ... | false = orAtomTo⊎' (evalRLit mod x) (evalRClause mod (lF \\ l)) (inj₁ x₁)
  ... | true = let
                 eq' : atom(l ==RLit x)
                 eq' = b≡trueImpliesb (l ==RLit x) eq

                 lTrue : T (evalRLit mod l)
                 lTrue = transfer==RLit' (λ y → T (evalRLit mod y)) l x eq' x₁

               in efq (ContradicLit mod l lTrue cT)

             -- eq  : (l ==RLit x) ≡ true
             -- b≡trueImpliesb (l ==RLit x) eq : atom(L ==RLit x)
  evalModaux1 mod l x lF cT (inj₂ y)  with (l ==RLit x) in eq
  ... | false = orAtomTo⊎' (evalRLit mod x) (evalRClause mod (lF \\ l))
                (inj₂ (evalMod mod l lF cT y))
  ... | true  = evalMod mod l lF cT y


evalMod' : (mod : RModel) (l : RLit)(c : RClause)
           (lF : EvalLit mod l)
           (cT : EvalRClause mod c)
           → EvalRClause mod (c \\ (negRLit l))
evalMod' mod l c lF cT = evalMod mod (negRLit l) c (LitImpliesNegNegL mod l lF) cT

resolutionLem1 : (mod : RModel)
                 (c c' : RClause)(l : RLit)
                 (p : EvalRClause mod c)
                 (q : EvalRClause mod c')
                 → EvalRClause mod (c \\ (negRLit l))
                    ⊎
                    EvalRClause mod (c' \\ l)
resolutionLem1 mod c c₁ l p q with RModelsLorNegL mod l
... | inj₁ lTrue    = inj₁ (evalMod' mod l c lTrue p)
... | inj₂ neglTrue = inj₂ (evalMod mod l c₁ neglTrue q)


nthRClauseImpliesListRClause : (mod : RModel)(as : RFor)
  (i : Fin (length as))
  (asT : EvalRFor mod as)
  → EvalRClause mod (nthFin as i)
nthRClauseImpliesListRClause mod (x ∷ as) zero asT = π₀ asT
nthRClauseImpliesListRClause mod (x ∷ as) (suc i) asT = nthRClauseImpliesListRClause mod as i (π₁ asT)

EntailsRFor : (as : RFor)(f : RFor) → Set
EntailsRFor as f = (mod : RModel) → EvalRFor mod as → EvalRFor mod f

EntailsRCl : (as : RFor)(c : RClause) → Set
EntailsRCl as c = (mod : RModel) → EvalRFor mod as → EvalRClause mod c

UnSatFor : RFor → Set
UnSatFor f = (mod : RModel) → EvalRFor mod f → ⊥

evalRClauseOr1 : (mod : RModel)(l : RLit)(c : RClause)
                → EvalLit mod l ⊎ EvalRClause mod c
                → EvalRClause mod (l ∷ c)
evalRClauseOr1 mod l c x = orAtomTo⊎' (evalRLit mod l) (evalRClause mod c) x

evalRClauseOr2 : (mod : RModel)(l : RLit)(c : RClause)
                → EvalRClause mod (l ∷ c)
                → EvalLit mod l ⊎ EvalRClause mod c
evalRClauseOr2 mod l c x = orAtomTo⊎ (evalRLit mod l) (evalRClause mod c) x

entailsUnfoldLeft₁ : (c₁ : RClause)(as : RFor)(c : RClause)
                       → EntailsRCl (c₁ ∷ as) c
                       → (mod : RModel) → EvalRFor mod as
                       → EvalRClause mod c₁
                       → EvalRClause mod c
entailsUnfoldLeft₁ c₁ as c p mod ast c₁t = p mod (π c₁t ast)

negRLitEval₁' : (mod : RModel)(l : RLit)
            → evalRLit mod (negRLit l) ≡ not (evalRLit mod l)
negRLitEval₁' mo (pos x) = refl
negRLitEval₁' mo (neg x) = doubleNotAtom₁' (evalRLit mo (negRLit (neg x)))

negRLitEval₁ : (mod : RModel)(l : RLit)
            → T (evalRLit mod (negRLit l)) → T (not (evalRLit mod l))
negRLitEval₁ mod (pos x) p = p
negRLitEval₁ mod (neg x) p = doubleNotAtom₁ (evalRVar mod x) p

negRLitEval₂ : (mod : RModel)(l : RLit)
            → T (not (evalRLit mod l))
            → T (evalRLit mod (negRLit l))
negRLitEval₂ mod (pos x) p = p
negRLitEval₂ mod (neg x) p = doubleNotAtom₂ (evalRVar mod x) p


entailsMoveFromAs2ConclSingle : (as : RFor)(l : RLit)(c : RClause)
                    → EntailsRCl (((negRLit l) ∷ []) ∷ as ) c
                    → EntailsRCl as  (l ∷ c)
entailsMoveFromAs2ConclSingle as l c p mod ev =
   let
      p1 : EvalRClause mod (negRLit l ∷ [])
                         → EvalRClause mod c
      p1 = entailsUnfoldLeft₁ (negRLit l ∷ []) as c p mod ev

      p2 : EvalLit mod (negRLit l) → EvalRClause mod (negRLit l ∷ [])
      p2 x = orAtomTo⊎' (evalRLit mod (negRLit l)) false (inj₁ x)

      p3 : EvalLit mod (negRLit l) → EvalRClause mod c
      p3 x = p1 (p2 x)

      p4 : atom (not (evalRLit mod l)) → EvalRClause mod c
      p4 x = p3 (negRLitEval₂ mod l x)

   in evalRClauseOr1 mod l c (notAr2Or (evalRLit mod l) p4 )


entailsMoveFromAs2ConclList : (as : RFor)(l : List RLit)(c : RClause)
                    → EntailsRCl (lits2RClauses (negRLits (reverseList l)) ++ as) c
                    → EntailsRCl as  (l ++ c)
entailsMoveFromAs2ConclList as [] c p = p
entailsMoveFromAs2ConclList as (l ∷ ls) c p
    = let
          p' : EntailsRCl
               (lits2RClauses (negRLits (reverseList ls ++ l ∷ [])) ++ as) c
          p' = p

          eq1 : negRLits (reverseList ls ++ l ∷ []) ≡
                  negRLits (reverseList ls) ++ (negRLit l ∷ [])
          eq1 = mapList++ negRLit (reverseList ls) (l ∷ [])

          eq1' : (lits2RClauses (negRLits (reverseList ls ++ l ∷ [])) ++ as)
                ≡ (lits2RClauses (negRLits (reverseList ls) ++ (negRLit l ∷ [])) ++ as)
          eq1' = cong≡ (λ x → lits2RClauses x ++ as) eq1

          p₂ : EntailsRCl (lits2RClauses (negRLits (reverseList ls) ++ (negRLit l ∷ [])) ++ as) c
          p₂ = transfer≡hid (λ y → EntailsRCl y c) eq1' p'

          eq2 : lits2RClauses (negRLits (reverseList ls) ++ (negRLit l) ∷ []) ≡
                  lits2RClauses (negRLits (reverseList ls)) ++
                  (((negRLit l) ∷ []) ∷ [])
          eq2 = mapList++ lit2RClause (negRLits (reverseList ls)) ((negRLit l) ∷ [])

          eq3 : (lits2RClauses (negRLits (reverseList ls) ++ (negRLit l ∷ [])) ++ as)
                ≡ (lits2RClauses (negRLits (reverseList ls)) ++
                  (((negRLit l) ∷ []) ∷ [])) ++ as
          eq3 = cong≡ (λ x → x ++ as) eq2

          eq4 : (lits2RClauses (negRLits (reverseList ls)) ++
                  (((negRLit l) ∷ []) ∷ [])) ++ as
                ≡
                (lits2RClauses (negRLits (reverseList ls)) ++
                  ((((negRLit l) ∷ []) ∷ [])) ++ as)
          eq4 = assoc++₁  (lits2RClauses (negRLits (reverseList ls)))
                         (((negRLit l) ∷ []) ∷ []) as

          eq5 : (lits2RClauses (negRLits (reverseList ls) ++ (negRLit l ∷ [])) ++ as)
                ≡ lits2RClauses (negRLits (reverseList ls)) ++
                  ((negRLit l ∷ []) ∷ as)
                  -- (((negRLit l) ∷ []) ∷ []) ++ as)
          eq5 = trans≡ eq3 eq4

          p3 : EntailsRCl (lits2RClauses (negRLits (reverseList ls)) ++
                  ((negRLit l ∷ []) ∷ as)) c
          p3 = transfer≡hid (λ y → EntailsRCl y c) eq5 p₂

          ih : EntailsRCl ((negRLit l ∷ []) ∷ as) (ls ++ c)
          ih = entailsMoveFromAs2ConclList ((negRLit l ∷ []) ∷ as) ls c p3

          p5 : EntailsRCl as (l ∷ (ls ++ c))
          p5 = entailsMoveFromAs2ConclSingle as l (ls ++ c) ih

      in p5

RForWith[]false : (f : RFor) → ([] ∈ f) →
                     (mod : RModel) → EvalRFor mod f → ⊥
RForWith[]false ((x ∷ x₁) ∷ f) p mod (π _ q) = RForWith[]false  f p mod q


RForWith[]NotEntailed : (as : RFor) (f : RFor) → ([] ∈ f)
                           → EntailsRFor as f
                           → UnSatFor as
RForWith[]NotEntailed as f p q mod r = RForWith[]false f p mod (q mod r)
