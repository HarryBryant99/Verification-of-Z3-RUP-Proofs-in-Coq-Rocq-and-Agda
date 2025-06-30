module rup.clause where

open import lib.boolLib
open import lib.eqLib
open import lib.finLib
open import lib.listLib
open import lib.natLib
open import lib.natLibBase
open import lib.prodLib
open import lib.vecLib

open import rup.variables

_==RVarS_ : RVar → RVar → Set
n ==RVarS m = atom (n ==RVar m)

instance
  EqVar : BoolEq RVar
  EqVar .eqb =  _==RVar_


transfer==RVar : (C : RVar → Set) →
                (n m : RVar) → n ==RVarS m → C n → C m
transfer==RVar C n m p = transfer≡ C n m (eqRVarTo== n m p)

transfer==RVar' : (C : RVar → Set) →
                (n m : RVar) → n ==RVarS m → C m → C n
transfer==RVar' C n m p = transfer≡' C n m (eqRVarTo== n m p)



data RLit : Set where
  pos : RVar → RLit
  neg : RVar → RLit

_==RLit_ : RLit → RLit → Bool
pos n ==RLit pos m =   n ==RVar m
neg n ==RLit neg m =   n ==RVar m
_     ==RLit _     =   false

_==RLitS_ : RLit → RLit → Set
n ==RLitS m = atom ( n ==RLit m)

transfer==RLit : (C : RLit → Set)
                (l l' : RLit) → l ==RLitS l' → C l → C l'
transfer==RLit C (pos x) (pos x₁) p c = transfer==RVar (λ n → C (pos n)) x x₁ p c
transfer==RLit C (neg x) (neg x₁) p c = transfer==RVar (λ n → C (neg n)) x x₁ p c


transfer==RLit' : (C : RLit → Set)
                (l l' : RLit) → l ==RLitS l' → C l' → C l
transfer==RLit' C (pos x) (pos x₁) p c = transfer==RVar' (λ n → C (pos n)) x x₁ p c
transfer==RLit' C (neg x) (neg x₁) p c = transfer==RVar' (λ n → C (neg n)) x x₁ p c

rlit2Var : RLit → RVar
rlit2Var (pos x) = x
rlit2Var (neg x) = x


instance
  EqLit : BoolEq RLit
  EqLit .eqb =  _==RLit_



negRLit : RLit → RLit
negRLit (pos v) = neg v
negRLit (neg v) = pos v

RClause : Set
RClause = List RLit

RFor : Set
RFor = List RClause

mergeCl : RClause → RClause → RClause
mergeCl = merge' {RLit} {{EqLit}}

emptyCl : RClause
emptyCl = []


isUnitCl : RClause → Bool
isUnitCl (_ ∷ []) = true
isUnitCl _ = false

isEmptyCl : RClause → Bool
isEmptyCl [] = true
isEmptyCl _ = false

-- nontrival clauses are clauses with
-- length >= 1
isNonTrivCl : RClause → Bool
isNonTrivCl [] = false
isNonTrivCl (_ ∷ []) = false
isNonTrivCl _ = true

isUnitRClauses : RFor → Bool
isUnitRClauses = all isUnitCl

isNonTrivRClauses : RFor → Bool
isNonTrivRClauses = all isNonTrivCl


IsUnitCl : RClause → Set
IsUnitCl c = atom (isUnitCl c)

IsEmptyCl : RClause → Set
IsEmptyCl c = atom (isEmptyCl c)

IsNonTrivCl : RClause → Set
IsNonTrivCl c = atom (isNonTrivCl c)

IsUnitRClauses : RFor → Set
IsUnitRClauses cl = atom (isUnitRClauses cl)

IsNonTrivRClauses : RFor → Set
IsNonTrivRClauses cl = atom (isNonTrivRClauses cl)

lit2RClause : RLit → RClause
lit2RClause l = l ∷ []

lits2RClauses : List  RLit → RFor
lits2RClauses  = mapList lit2RClause


-- get alist of RVars in a clause with no duplicates

rclause2Vars : RClause → List RVar
rclause2Vars [] = []
rclause2Vars (x ∷ c) = rlit2Var x ∷noDup rclause2Vars c

rclauses2Vars : RFor → List RVar
rclauses2Vars [] = []
rclauses2Vars (x ∷ l) = rclause2Vars x ++noDup  rclauses2Vars l

#varsInRClauses : RFor → ℕ
#varsInRClauses l = length (rclauses2Vars l)

negRLits : RClause → RClause
negRLits = mapList negRLit
