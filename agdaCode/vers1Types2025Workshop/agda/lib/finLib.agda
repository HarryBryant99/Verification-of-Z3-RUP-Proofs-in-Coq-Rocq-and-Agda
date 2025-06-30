module lib.finLib where

open import lib.eqLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib

-- Fin n is a type with n elements.
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)


transferZerop : (k n : ℕ) (kn : suc k ≡ suc n)
               → transfer≡' Fin (suc k) (suc n) kn zero ≡ zero
transferZerop n n refl = refl

tranferSucp : (k n : ℕ) (kn : suc k ≡ suc n)(i : Fin n)
              → transfer≡' Fin (suc k) (suc n) kn (suc i)
                 ≡ suc (transfer≡' Fin k n (sucInj kn) i)
tranferSucp k .k refl i = refl
