module lib.natLibBase where

open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ;_==_ to _≡ᵇ_)
