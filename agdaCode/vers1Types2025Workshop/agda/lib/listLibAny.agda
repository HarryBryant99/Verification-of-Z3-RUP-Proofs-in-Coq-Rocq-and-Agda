module lib.listLibAny where

open import lib.boolLib

open import Agda.Builtin.List public
  using (List; []; _∷_)

infixr 9 _∘_

_∘_ : ∀ {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs


foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

or : List Bool → Bool
or = foldr _∨b_ false

and : List Bool → Bool
and = foldr _∧b_ true


any : {A : Set} → (A → Bool) → List A → Bool
any p = or ∘ map p

all : {A : Set} → (A → Bool) → List A → Bool
all p = and ∘ map p
