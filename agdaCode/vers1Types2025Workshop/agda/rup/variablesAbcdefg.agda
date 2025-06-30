module rup.variablesAbcdefg where

open import lib.boolLib
open import lib.eqLib


data Variable : Set  where
  a' b' c' d' e' f' g' : Variable

_==Var_ : Variable → Variable → Bool
a' ==Var a' = true
b' ==Var b' = true
c' ==Var c' = true
d' ==Var d' = true
e' ==Var e' = true
f' ==Var f' = true
g' ==Var g' = true
_ ==Var _ = false


-- The following causes problems in my current version of Agda
-- because AGda doesn't see that
-- atom (a' ==Var a')
-- reduces to Agda.Builtin.Unit.⊤
-- and therefore tt is an element of that type
-- This might be fixed in a later version


eqVarTo== : (a b : Variable) → atom (a ==Var b) → a ≡ b
eqVarTo== a' a' tt = refl
eqVarTo== b' b' tt = refl
eqVarTo== c' c' tt = refl
eqVarTo== d' d' tt = refl
eqVarTo== e' e' tt = refl
eqVarTo== f' f' tt = refl
eqVarTo== g' g' tt = refl

{-
transfer==Var : (C : Variable → Set) →
                (n m : Variable) → atom (n ==Var m) → C n → C m
transfer==Var C a' a' tt c = c
transfer==Var C b' b' tt c = c
transfer==Var C c' c' tt c = c
transfer==Var C d' d' tt c = c
transfer==Var C e' e' tt c = c
transfer==Var C f' f' tt c = c
transfer==Var C g' g' tt c = c

transfer==Var' : (C : Variable → Set) →
                (n m : Variable) → atom (n ==Var m) → C m → C n
transfer==Var' C a' a' tt c = c
transfer==Var' C b' b' tt c = c
transfer==Var' C c' c' tt c = c
transfer==Var' C d' d' tt c = c
transfer==Var' C e' e' tt c = c
transfer==Var' C f' f' tt c = c
transfer==Var' C g' g' tt c = c
-}
