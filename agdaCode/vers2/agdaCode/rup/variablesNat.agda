module rup.variablesNat where

open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib

RVar : Set
RVar = ℕ

_==RVar_ : RVar → RVar → Bool
_==RVar_ =  _≡ᵇ_

eqRVarTo== : (n m : RVar) → atom (n ==RVar m) → n ≡ m
eqRVarTo== = eqℕTo≡


{-
transfer==RVar : (C : RVar → Set) →
                (n m : RVar) → atom (n ==RVar m) → C n → C m
transfer==RVar = transferEqℕ

transfer==RVar' : (C : RVar → Set) →
                (n m : RVar) → atom (n ==RVar m) → C n → C m
transfer==RVar' = transferEqℕ
-}
