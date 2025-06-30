module lib.sumLib where

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B
