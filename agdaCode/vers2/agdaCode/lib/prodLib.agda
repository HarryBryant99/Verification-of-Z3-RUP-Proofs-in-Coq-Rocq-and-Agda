module lib.prodLib where

record _∧s_ (A B : Set) : Set where
  constructor _andp_
  field
     fst : A
     snd : B
open _∧s_ public

record _×_ (A B : Set) : Set where
  constructor π
  field
     fst : A
     snd : B
open _×_ public

π₀ : {A B : Set} → A × B → A
π₀ (π a b) = a

π₁ : {A B : Set} → A × B → B
π₁ (π a b) = b
