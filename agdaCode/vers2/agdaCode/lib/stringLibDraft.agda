Use from Data.String.Properties


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
