module lib.natLib where

open import lib.eqLib
open import lib.boolLib
open import lib.eqLib
open import lib.unitLib
open import lib.natLibBase



sucInj : {n m : ℕ}(nm : suc n ≡ suc m) → n ≡ m
sucInj {n} {.n} refl = refl

sucInjCor : {n m : ℕ}(nm : n ≡ m)
            → sucInj (cong≡ suc nm) ≡ nm
sucInjCor refl = refl

reflEq : (n : ℕ) → n == n
reflEq zero = tt
reflEq (suc n) = reflEq n


transferEqℕ  : (C : ℕ → Set) (n m : ℕ)(p : atom (n ≡ᵇ m)) → C n → C m
transferEqℕ C zero zero p c = c
transferEqℕ C (suc n) (suc m) p c = transferEqℕ (λ n → C (suc n)) n m p c

transferEqℕ'  : (C : ℕ → Set) (n m : ℕ)(p : atom (n ≡ᵇ m)) → C m → C n
transferEqℕ' C zero zero p c = c
transferEqℕ' C (suc n) (suc m) p c = transferEqℕ' (λ n → C (suc n)) n m p c

eqℕTo≡ : (n m : ℕ) → atom (n ≡ᵇ  m) → n ≡ m
eqℕTo≡ zero zero p = refl
eqℕTo≡ (suc n) (suc m) p = cong≡ suc (eqℕTo≡ n m p)
