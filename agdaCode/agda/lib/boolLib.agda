module lib.boolLib where

open import lib.prodLib
open import lib.sumLib
open import lib.unitLib
open import lib.emptyLib
open import lib.eqLib
open import lib.natLibBase

open import Agda.Builtin.Bool public


T : Bool → Set
T true  = ⊤
T false = ⊥

not : Bool → Bool
not true  = false
not false = true

_∧b_ : Bool → Bool → Bool
true  ∧b b = b
false ∧b b = false

_∨b_ : Bool → Bool → Bool
true  ∨b b = true
false ∨b b = b


atom : Bool → Set
atom = T

IsFalse  : Bool → Set
IsFalse b = atom (not b)

tertiumNonD : (b : Bool) → atom b ⊎ atom (not b)
tertiumNonD false =  inj₂ tt
tertiumNonD true = inj₁ tt

tertiumNonD' : (b : Bool) → atom (not b) ⊎ atom b
tertiumNonD' false =  inj₁ tt
tertiumNonD' true = inj₂ tt

doubleNotAtom₁ : (b : Bool) → atom b → atom (not (not b))
doubleNotAtom₁ true p = tt

doubleNotAtom₂ : (b : Bool) → atom (not (not b)) → atom b
doubleNotAtom₂ true p = tt

orAtomTo⊎ : (b b' : Bool) → atom ( b ∨b b') → atom b ⊎ atom b'
orAtomTo⊎ false b' p = inj₂ p
orAtomTo⊎ true b'  _ = inj₁ tt

orAtomTo⊎' : (b b' : Bool) → atom b ⊎ atom b' → atom ( b ∨b b')
orAtomTo⊎' false b' (inj₂ y) = y
orAtomTo⊎' true b'  _ = tt

contradictBool : (b : Bool) → atom b → atom (not b) → ⊥
contradictBool false p p' = p
contradictBool true p p' = p'

efq : {C : Set} → ⊥ → C
efq ()

or⊥₁ : {A : Set} → A ⊎ ⊥ → A
or⊥₁ (inj₁ x) = x


b≡trueImpliesb : (b : Bool) → b ≡ true → atom b
b≡trueImpliesb true p = tt

record BoolEq (A : Set) : Set where
 field
   eqb : A → A → Bool
open BoolEq public

_==b_ : {A : Set}{{eqA : BoolEq A}} → A → A → Bool
_==b_ {A} {{eqA}} = eqA .eqb

_==_ : {A : Set}{{eqA : BoolEq A}} → A → A → Set
_==_ a a' = atom ( a ==b a')

instance
  EqNat : BoolEq ℕ
  EqNat .eqb =  _≡ᵇ_

∧b-elim1 : (b1 b2 : Bool) → atom (b1 ∧b b2) → atom b1
∧b-elim1 true b2 p = tt

∧b-elim2 : (b1 b2 : Bool) → atom (b1 ∧b b2) → atom b2
∧b-elim2 true true _ = tt

∧b-to-∧ : {b1 b2 : Bool} → atom (b1 ∧b b2) → atom b1 ∧s atom b2
∧b-to-∧  {true} {true} _ = tt andp tt

∧b3-to-∧ : {b1 b2 b3 : Bool} → atom (b1 ∧b (b2 ∧b b3)) → atom b1 ∧s (atom b2 ∧s atom b3)
∧b3-to-∧ {true} {true} {true} _ =  tt andp (tt andp tt)

_<b_ : ℕ → ℕ → Bool
_     <b zero    = false
zero  <b (suc _) = true
suc n <b suc m   = n <b m

-- In Coq result probably Prop
_<'_ : ℕ → ℕ → Set
n <' m = atom ( n <b m)


notAr2Or : {A : Set}(b : Bool) (p : atom (not b) → A) → atom b ⊎ A
notAr2Or false p = inj₂ (p tt)
notAr2Or true p = inj₁ tt
