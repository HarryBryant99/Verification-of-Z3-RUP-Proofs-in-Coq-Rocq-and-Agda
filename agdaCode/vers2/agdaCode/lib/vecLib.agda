module lib.vecLib where

open import lib.eqLib
open import lib.natLib
open import lib.natLibBase
open import lib.finLib
open import lib.eqLib

infixr 5 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


mapVec : {A B : Set}(f : A → B){n : ℕ}(v : Vec A n) → Vec B n
mapVec f [] = []
mapVec f (x ∷ l) = f x ∷ mapVec f l

nthVec : {A : Set}{n : ℕ}(v : Vec A n)(k : Fin n) → A
nthVec (x ∷ v) zero = x
nthVec (x ∷ v) (suc k) = nthVec v k

mapVecNthCor : {A B : Set}(f : A → B){n : ℕ}(v : Vec A n)(k : Fin n)
               → nthVec (mapVec f v) k ≡ f (nthVec v k)
mapVecNthCor f (x ∷ v) zero = refl
mapVecNthCor f (x ∷ v) (suc k) = mapVecNthCor f v k

finVec : (n : ℕ) → Vec (Fin n)  n
finVec zero = []
finVec (suc n) = zero ∷ mapVec suc (finVec n)

corFinVec : (n : ℕ) (k : Fin n) → nthVec (finVec n) k ≡ k
corFinVec (suc n) zero = refl
corFinVec (suc n) (suc k) =
     let
        p : nthVec (mapVec {Fin n}{Fin (suc n)} suc (finVec n)) k
            ≡ suc (nthVec (finVec n) k)
        p = mapVecNthCor suc (finVec n) k

        q : suc (nthVec (finVec n) k) ≡ suc k
        q = cong≡ {Fin n}{Fin (suc n)} suc (corFinVec n k)

     in trans≡ p q
