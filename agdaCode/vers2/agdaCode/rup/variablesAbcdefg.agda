module rup.variablesAbcdefg where

open import lib.boolLib
open import lib.eqLib


data RVar : Set  where
  a' b' c' d' e' f' g' : RVar

_==RVar_ : RVar → RVar → Bool
a' ==RVar a' = true
b' ==RVar b' = true
c' ==RVar c' = true
d' ==RVar d' = true
e' ==RVar e' = true
f' ==RVar f' = true
g' ==RVar g' = true
_ ==RVar _ = false

eqRVarTo== : (a b : RVar) → atom (a ==RVar b) → a ≡ b
eqRVarTo== a' a' tt = refl
eqRVarTo== b' b' tt = refl
eqRVarTo== c' c' tt = refl
eqRVarTo== d' d' tt = refl
eqRVarTo== e' e' tt = refl
eqRVarTo== f' f' tt = refl
eqRVarTo== g' g' tt = refl

{-
transfer==RVar : (C : RVar → Set) →
                (n m : RVar) → atom (n ==RVar m) → C n → C m
transfer==RVar C a' a' tt c = c
transfer==RVar C b' b' tt c = c
transfer==RVar C c' c' tt c = c
transfer==RVar C d' d' tt c = c
transfer==RVar C e' e' tt c = c
transfer==RVar C f' f' tt c = c
transfer==RVar C g' g' tt c = c

transfer==RVar' : (C : RVar → Set) →
                (n m : RVar) → atom (n ==RVar m) → C m → C n
transfer==RVar' C a' a' tt c = c
transfer==RVar' C b' b' tt c = c
transfer==RVar' C c' c' tt c = c
transfer==RVar' C d' d' tt c = c
transfer==RVar' C e' e' tt c = c
transfer==RVar' C f' f' tt c = c
transfer==RVar' C g' g' tt c = c
-}
