module lib.stringLib where

open import Data.String
open import Data.String.Properties
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Reflects
open import Data.List.Relation.Binary.Pointwise.Properties
open import Agda.Builtin.Char.Properties
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Char
open import Data.Nat.Properties hiding (_≟_ )
open import lib.eqLib
open import lib.boolLib

{-
tmp1 : DecidableEquality String
tmp1 = _≟_

tmp2 : (x y : String) → Dec (x ≡ y)
tmp2 = _≟_
-}
_==str_ : String → String → Bool
s ==str t =  (s ≟ t) .does

reflects==str : (s t : String) → Reflects (s ≡ t) (s ==str t)
reflects==str s t = (s ≟ t) .proof

fromReflectsTrue : {A : Set} → Reflects A true → A
fromReflectsTrue (ofʸ a) = a

fromReflects : {A : Set}(b : Bool) → T b → Reflects A b → A
fromReflects {A} true x (ofʸ a) = a

==strTo≡  : (s t : String) → T (s ==str t) → s ≡ t
==strTo≡ s t p  = fromReflects (s ==str t) p ((s ≟ t) .proof)


{-
infix 4 _==_
_==_ : String → String → Bool
s₁ == s₂ = isYes (s₁ ≟ s₂)

_≟_ : DecidableEquality String
x ≟ y = map′ ≈⇒≡ ≈-reflexive $ x ≈? y

DecidableEquality : (A : Set a) → Set _
DecidableEquality A = Decidable {A = A} _≡_

Decidable : REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)


record Dec (A : Set a) : Set a where
  constructor _because_
  field
    does  : Bool
    proof : Reflects A does

data Reflects (A : Set a) : Bool → Set a where
  ofʸ : ( a :   A) → Reflects A true
  ofⁿ : (¬a : ¬ A) → Reflects A false
-}
