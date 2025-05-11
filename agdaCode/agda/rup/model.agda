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


Model : Set
Model = Variable → Bool

evalVar : Model → Variable → Bool
evalVar mod v = mod v

EvalVar : Model → Variable → Set
EvalVar mod v = atom (evalVar mod v)

evalLit : Model → Literal → Bool
evalLit mod (pos v) = evalVar mod v
evalLit mod (neg v) = not (evalVar mod v)

EvalLit : Model → Literal → Set
EvalLit mod v = atom (evalLit mod v)

evalClause : Model → Clause → Bool
evalClause mod [] = false
evalClause mod (l ∷ ls) = evalLit mod l ∨b evalClause mod ls

EvalClause : Model → Clause → Set
EvalClause mod v = atom (evalClause mod v)


evalUnitClauseToUnit : (mod : Model)(l : Literal)
                       → EvalClause mod (l ∷ [])
                       → EvalLit mod l
evalUnitClauseToUnit mod l p =
    let
       p' :  atom (evalLit mod l) ⊎ atom false
       p' = orAtomTo⊎ (evalLit mod l) false p
    in  or⊥₁ p'

EvalFormula : Model → Formula → Set
EvalFormula mod [] = ⊤
EvalFormula mod (l ∷ ls) = EvalClause mod l × EvalFormula mod ls


EmptyClauseFalse : (mod : Model) → IsFalse (evalClause mod [])
EmptyClauseFalse mod = tt

ModelsLorNegL : (mod : Model) (l : Literal) → EvalLit mod l ⊎ EvalLit mod (negL l)
ModelsLorNegL mod (pos x) = tertiumNonD (mod x)
ModelsLorNegL mod (neg x) = tertiumNonD' (mod x)

ContradicLit : (mod : Model) (l : Literal) → EvalLit mod l
               → EvalLit mod (negL l) → ⊥
ContradicLit mod (pos x) p p' = contradictBool (mod x) p p'
ContradicLit mod (neg x) p p' = contradictBool (mod x) p' p

LitImpliesNegNegL  : (mod :  Model) (l : Literal)
                     → EvalLit mod l
                     → EvalLit mod (negL (negL l))
LitImpliesNegNegL mod (pos x) p = p
LitImpliesNegNegL mod (neg x) p = p


mutual
  evalMod : (mod : Model) (l : Literal)(c : Clause)
            (lF : EvalLit mod (negL l))
            (cT : EvalClause mod c)
            → EvalClause mod (c \\ l)
  evalMod mod l (x ∷ c) lF cT = evalModaux1 mod l x c lF (orAtomTo⊎ (evalLit mod x)(evalClause mod c) cT)
  -- T (evalClause mod (setminusAux x c l (l ==Lit x)))

  evalModaux1 : (mod : Model) (l x : Literal)(c : Clause)
            (lF : EvalLit mod (negL l))
            (cT : EvalLit mod x ⊎ EvalClause mod c)
            → EvalClause mod (setminusAux x c l (l ==Lit x))
  evalModaux1 mod l x lF cT (inj₁ x₁) with (l ==Lit x) in eq
  ... | false = orAtomTo⊎' (evalLit mod x) (evalClause mod (lF \\ l)) (inj₁ x₁)
  ... | true = let
                 eq' : atom(l ==Lit x)
                 eq' = b≡trueImpliesb (l ==Lit x) eq

                 lTrue : T (evalLit mod l)
                 lTrue = transfer==Lit' (λ y → T (evalLit mod y)) l x eq' x₁

               in efq (ContradicLit mod l lTrue cT)

             -- eq  : (l ==Lit x) ≡ true
             -- b≡trueImpliesb (l ==Lit x) eq : atom(L ==Lit x)
  evalModaux1 mod l x lF cT (inj₂ y)  with (l ==Lit x) in eq
  ... | false = orAtomTo⊎' (evalLit mod x) (evalClause mod (lF \\ l))
                (inj₂ (evalMod mod l lF cT y))
  ... | true  = evalMod mod l lF cT y


evalMod' : (mod : Model) (l : Literal)(c : Clause)
           (lF : EvalLit mod l)
           (cT : EvalClause mod c)
           → EvalClause mod (c \\ (negL l))
evalMod' mod l c lF cT = evalMod mod (negL l) c (LitImpliesNegNegL mod l lF) cT

resolutionLem1 : (mod : Model)
                 (c c' : Clause)(l : Literal)
                 (p : EvalClause mod c)
                 (q : EvalClause mod c')
                 → EvalClause mod (c \\ (negL l))
                    ⊎
                    EvalClause mod (c' \\ l)
resolutionLem1 mod c c₁ l p q with ModelsLorNegL mod l
... | inj₁ lTrue    = inj₁ (evalMod' mod l c lTrue p)
... | inj₂ neglTrue = inj₂ (evalMod mod l c₁ neglTrue q)


nthClauseImpliesListClause : (mod : Model)(as : Formula)
  (i : Fin (length as))
  (asT : EvalFormula mod as)
  → EvalClause mod (nthFin as i)
nthClauseImpliesListClause mod (x ∷ as) zero asT = π₀ asT
nthClauseImpliesListClause mod (x ∷ as) (suc i) asT = nthClauseImpliesListClause mod as i (π₁ asT)

EntailsFor : (as : Formula)(f : Formula) → Set
EntailsFor as f = (mod : Model) → EvalFormula mod as → EvalFormula mod f

EntailsCl : (as : Formula)(c : Clause) → Set
EntailsCl as c = (mod : Model) → EvalFormula mod as → EvalClause mod c

UnSatFor : Formula → Set
UnSatFor f = (mod : Model) → EvalFormula mod f → ⊥

evalClauseOr1 : (mod : Model)(l : Literal)(c : Clause)
                → EvalLit mod l ⊎ EvalClause mod c
                → EvalClause mod (l ∷ c)
evalClauseOr1 mod l c x = orAtomTo⊎' (evalLit mod l) (evalClause mod c) x

evalClauseOr2 : (mod : Model)(l : Literal)(c : Clause)
                → EvalClause mod (l ∷ c)
                → EvalLit mod l ⊎ EvalClause mod c
evalClauseOr2 mod l c x = orAtomTo⊎ (evalLit mod l) (evalClause mod c) x

entailsUnfoldLeft₁ : (c₁ : Clause)(as : Formula)(c : Clause)
                       → EntailsCl (c₁ ∷ as) c
                       → (mod : Model) → EvalFormula mod as
                       → EvalClause mod c₁
                       → EvalClause mod c
entailsUnfoldLeft₁ c₁ as c p mod ast c₁t = p mod (π c₁t ast)


negLEval₁ : (mod : Model)(l : Literal)
            → T (evalLit mod (negL l)) → T (not (evalLit mod l))
negLEval₁ mod (pos x) p = p
negLEval₁ mod (neg x) p = doubleNotAtom₁ (evalVar mod x) p

negLEval₂ : (mod : Model)(l : Literal)
            → T (not (evalLit mod l))
            → T (evalLit mod (negL l))
negLEval₂ mod (pos x) p = p
negLEval₂ mod (neg x) p = doubleNotAtom₂ (evalVar mod x) p


entailsMoveFromAs2ConclSingle : (as : Formula)(l : Literal)(c : Clause)
                    → EntailsCl (((negL l) ∷ []) ∷ as ) c
                    → EntailsCl as  (l ∷ c)
entailsMoveFromAs2ConclSingle as l c p mod ev =
   let
      p1 : EvalClause mod (negL l ∷ [])
                         → EvalClause mod c
      p1 = entailsUnfoldLeft₁ (negL l ∷ []) as c p mod ev

      p2 : EvalLit mod (negL l) → EvalClause mod (negL l ∷ [])
      p2 x = orAtomTo⊎' (evalLit mod (negL l)) false (inj₁ x)

      p3 : EvalLit mod (negL l) → EvalClause mod c
      p3 x = p1 (p2 x)

      p4 : atom (not (evalLit mod l)) → EvalClause mod c
      p4 x = p3 (negLEval₂ mod l x)

   in evalClauseOr1 mod l c (notAr2Or (evalLit mod l) p4 )


entailsMoveFromAs2ConclList : (as : Formula)(l : List Literal)(c : Clause)
                    → EntailsCl (lits2Clauses (negLits (reverseList l)) ++ as) c
                    → EntailsCl as  (l ++ c)
entailsMoveFromAs2ConclList as [] c p = p
entailsMoveFromAs2ConclList as (l ∷ ls) c p
    = let
          p' : EntailsCl
               (lits2Clauses (negLits (reverseList ls ++ l ∷ [])) ++ as) c
          p' = p

          eq1 : negLits (reverseList ls ++ l ∷ []) ≡
                  negLits (reverseList ls) ++ (negL l ∷ [])
          eq1 = mapList++ negL (reverseList ls) (l ∷ [])

          eq1' : (lits2Clauses (negLits (reverseList ls ++ l ∷ [])) ++ as)
                ≡ (lits2Clauses (negLits (reverseList ls) ++ (negL l ∷ [])) ++ as)
          eq1' = cong≡ (λ x → lits2Clauses x ++ as) eq1

          p₂ : EntailsCl (lits2Clauses (negLits (reverseList ls) ++ (negL l ∷ [])) ++ as) c
          p₂ = transfer≡hid (λ y → EntailsCl y c) eq1' p'

          eq2 : lits2Clauses (negLits (reverseList ls) ++ (negL l) ∷ []) ≡
                  lits2Clauses (negLits (reverseList ls)) ++
                  (((negL l) ∷ []) ∷ [])
          eq2 = mapList++ lit2Clause (negLits (reverseList ls)) ((negL l) ∷ [])

          eq3 : (lits2Clauses (negLits (reverseList ls) ++ (negL l ∷ [])) ++ as)
                ≡ (lits2Clauses (negLits (reverseList ls)) ++
                  (((negL l) ∷ []) ∷ [])) ++ as
          eq3 = cong≡ (λ x → x ++ as) eq2

          eq4 : (lits2Clauses (negLits (reverseList ls)) ++
                  (((negL l) ∷ []) ∷ [])) ++ as
                ≡
                (lits2Clauses (negLits (reverseList ls)) ++
                  ((((negL l) ∷ []) ∷ [])) ++ as)
          eq4 = assoc++₁  (lits2Clauses (negLits (reverseList ls)))
                         (((negL l) ∷ []) ∷ []) as

          eq5 : (lits2Clauses (negLits (reverseList ls) ++ (negL l ∷ [])) ++ as)
                ≡ lits2Clauses (negLits (reverseList ls)) ++
                  ((negL l ∷ []) ∷ as)
                  -- (((negL l) ∷ []) ∷ []) ++ as)
          eq5 = trans≡ eq3 eq4

          p3 : EntailsCl (lits2Clauses (negLits (reverseList ls)) ++
                  ((negL l ∷ []) ∷ as)) c
          p3 = transfer≡hid (λ y → EntailsCl y c) eq5 p₂

          ih : EntailsCl ((negL l ∷ []) ∷ as) (ls ++ c)
          ih = entailsMoveFromAs2ConclList ((negL l ∷ []) ∷ as) ls c p3

          p5 : EntailsCl as (l ∷ (ls ++ c))
          p5 = entailsMoveFromAs2ConclSingle as l (ls ++ c) ih

      in p5

FormulaWith[]false : (f : Formula) → ([] ∈ f) →
                     (mod : Model) → EvalFormula mod f → ⊥
FormulaWith[]false ((x ∷ x₁) ∷ f) p mod (π _ q) = FormulaWith[]false  f p mod q


FormulaWith[]NotEntailed : (as : Formula) (f : Formula) → ([] ∈ f)
                           → EntailsFor as f
                           → UnSatFor as
FormulaWith[]NotEntailed as f p q mod r = FormulaWith[]false f p mod (q mod r)
