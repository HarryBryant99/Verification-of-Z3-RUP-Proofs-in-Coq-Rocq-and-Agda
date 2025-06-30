module rup.preProofsAndCheckingUnused where

open import rup.preProofsAndChecking

∧b-elim4-last : (b1 b2 b3 b4 : Bool) → atom (b1 ∧b (b2 ∧b (b3 ∧b b4))) → atom b4
∧b-elim4-last b1 b2 b3 b4 p =
   ∧b-elim2 b3 b4
   (∧b-elim2 b2 (b3 ∧b b4)
    (∧b-elim2 b1 (b2 ∧b (b3 ∧b b4)) p))

∧b-elim4-3rd : (b1 b2 b3 b4 : Bool) → atom (b1 ∧b (b2 ∧b (b3 ∧b b4))) → atom b3
∧b-elim4-3rd b1 b2 b3 b4 p =
   ∧b-elim1 b3 b4
   (∧b-elim2 b2 (b3 ∧b b4)
    (∧b-elim2 b1 (b2 ∧b (b3 ∧b b4)) p))

∧b-elim4-2nd : (b1 b2 b3 b4 : Bool) → atom (b1 ∧b (b2 ∧b (b3 ∧b b4))) → atom b2
∧b-elim4-2nd b1 b2 b3 b4 p =
   ∧b-elim1 b2 (b3 ∧b b4)
    (∧b-elim2 b1 (b2 ∧b (b3 ∧b b4)) p)

∧b-elim4-1st : (b1 b2 b3 b4 : Bool) → atom (b1 ∧b (b2 ∧b (b3 ∧b b4))) → atom b1
∧b-elim4-1st b1 b2 b3 b4 p =
    ∧b-elim1 b1 (b2 ∧b (b3 ∧b b4)) p
