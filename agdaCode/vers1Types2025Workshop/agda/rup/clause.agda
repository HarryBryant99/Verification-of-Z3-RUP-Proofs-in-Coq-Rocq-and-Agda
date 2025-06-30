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

_==VarS_ : Variable → Variable → Set
n ==VarS m = atom (n ==Var m)

instance
  EqVar : BoolEq Variable
  EqVar .eqb =  _==Var_


transfer==Var : (C : Variable → Set) →
                (n m : Variable) → n ==VarS m → C n → C m
transfer==Var C n m p = transfer≡ C n m (eqVarTo== n m p)

transfer==Var' : (C : Variable → Set) →
                (n m : Variable) → n ==VarS m → C m → C n
transfer==Var' C n m p = transfer≡' C n m (eqVarTo== n m p)



data Literal : Set where
  pos : Variable → Literal
  neg : Variable → Literal

_==Lit_ : Literal → Literal → Bool
pos n ==Lit pos m =   n ==Var m
neg n ==Lit neg m =   n ==Var m
_     ==Lit _     =   false

_==LitS_ : Literal → Literal → Set
n ==LitS m = atom ( n ==Lit m)

transfer==Lit : (C : Literal → Set)
                (l l' : Literal) → l ==LitS l' → C l → C l'
transfer==Lit C (pos x) (pos x₁) p c = transfer==Var (λ n → C (pos n)) x x₁ p c
transfer==Lit C (neg x) (neg x₁) p c = transfer==Var (λ n → C (neg n)) x x₁ p c


transfer==Lit' : (C : Literal → Set)
                (l l' : Literal) → l ==LitS l' → C l' → C l
transfer==Lit' C (pos x) (pos x₁) p c = transfer==Var' (λ n → C (pos n)) x x₁ p c
transfer==Lit' C (neg x) (neg x₁) p c = transfer==Var' (λ n → C (neg n)) x x₁ p c

lit2Var : Literal → Variable
lit2Var (pos x) = x
lit2Var (neg x) = x


instance
  EqLit : BoolEq Literal
  EqLit .eqb =  _==Lit_



negL : Literal → Literal
negL (pos v) = neg v
negL (neg v) = pos v

Clause : Set
Clause = List Literal

Formula : Set
Formula = List Clause

mergeCl : Clause → Clause → Clause
mergeCl = merge' {Literal} {{EqLit}}

emptyCl : Clause
emptyCl = []


isUnitCl : Clause → Bool
isUnitCl (_ ∷ []) = true
isUnitCl _ = false

isEmptyCl : Clause → Bool
isEmptyCl [] = true
isEmptyCl _ = false

-- nontrival clauses are clauses with
-- length >= 1
isNonTrivCl : Clause → Bool
isNonTrivCl [] = false
isNonTrivCl (_ ∷ []) = false
isNonTrivCl _ = true

isUnitClauses : Formula → Bool
isUnitClauses = all isUnitCl

isNonTrivClauses : Formula → Bool
isNonTrivClauses = all isNonTrivCl


IsUnitCl : Clause → Set
IsUnitCl c = atom (isUnitCl c)

IsEmptyCl : Clause → Set
IsEmptyCl c = atom (isEmptyCl c)

IsNonTrivCl : Clause → Set
IsNonTrivCl c = atom (isNonTrivCl c)

IsUnitClauses : Formula → Set
IsUnitClauses cl = atom (isUnitClauses cl)

IsNonTrivClauses : Formula → Set
IsNonTrivClauses cl = atom (isNonTrivClauses cl)

lit2Clause : Literal → Clause
lit2Clause l = l ∷ []

lits2Clauses : List  Literal → Formula
lits2Clauses  = mapList lit2Clause


-- get alist of Variables in a clause with no duplicates

clause2Vars : Clause → List Variable
clause2Vars [] = []
clause2Vars (x ∷ c) = lit2Var x ∷noDup clause2Vars c

clauses2Vars : Formula → List Variable
clauses2Vars [] = []
clauses2Vars (x ∷ l) = clause2Vars x ++noDup  clauses2Vars l

#varsInClauses : Formula → ℕ
#varsInClauses l = length (clauses2Vars l)

negLits : Clause → Clause
negLits = mapList negL
