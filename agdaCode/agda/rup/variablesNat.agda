module rup.variablesNat where

open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib

Variable : Set
Variable = ℕ

_==Var_ : Variable → Variable → Bool
_==Var_ =  _≡ᵇ_

eqVarTo== : (n m : Variable) → atom (n ==Var m) → n ≡ m
eqVarTo== = eqℕTo≡


{-
transfer==Var : (C : Variable → Set) →
                (n m : Variable) → atom (n ==Var m) → C n → C m
transfer==Var = transferEqℕ

transfer==Var' : (C : Variable → Set) →
                (n m : Variable) → atom (n ==Var m) → C n → C m
transfer==Var' = transferEqℕ
-}
