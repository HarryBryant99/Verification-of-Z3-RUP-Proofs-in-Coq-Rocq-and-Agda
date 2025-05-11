module lib.eqLib where

open import Agda.Builtin.Equality public

transfer≡ : {A : Set}(C : A → Set)(a b : A)(ab : a ≡ b) → C a → C b
transfer≡  C a b refl p = p

transfer≡' : {A : Set}(C : A → Set)(a b : A)(ab : a ≡ b) → C b → C a
transfer≡'  C a b refl p = p

transfer≡hid : {A : Set}(C : A → Set){a b : A}(ab : a ≡ b) → C a → C b
transfer≡hid  C {a} {b} refl p = p

transfer≡'hid : {A : Set}(C : A → Set){a b : A}(ab : a ≡ b) → C b → C a
transfer≡'hid  C {a} {b} refl p = p

cong≡  : {A B : Set}(f : A → B){a a' : A}(aa' : a ≡ a') → f a ≡ f a'
cong≡  f refl = refl

trans≡  : {A : Set}{a b c : A}(ab : a ≡ b)(bc : b ≡ c) → a ≡ c
trans≡  refl refl = refl
