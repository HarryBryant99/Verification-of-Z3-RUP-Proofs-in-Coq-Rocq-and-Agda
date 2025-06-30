module lib.listLib where

open import lib.boolLib
open import lib.eqLib
open import lib.finLib
open import lib.natLib
open import lib.natLibBase
open import lib.boolLib

open import Agda.Builtin.List public
  using (List; []; _∷_)

any : {A : Set} → (A → Bool) → List A → Bool
any f [] = false
any f (x ∷ l) = f x ∨b any f l

all : {A : Set} → (A → Bool) → List A → Bool
all f [] = true
all f (x ∷ l) = f x ∧b all f l


_∈b_ : {A : Set}{{eqA : BoolEq A}}(a : A) (l : List A) → Bool
_∈b_ {A} {{eqA}} a l = any (eqA .eqb a) l

_∉b_ : {A : Set}{{eqA : BoolEq A}}(a : A) (l : List A) → Bool
a ∉b b = not (a ∈b b)


_∈_ : {A : Set}{{eqA : BoolEq A}}(a : A) (l : List A) → Set
a ∈ l = atom (a ∈b l)

_∉_ : {A : Set}{{eqA : BoolEq A}}(a : A) (l : List A) → Set
a ∉ l = atom (a ∉b l)

_⊆_ : {A : Set}{{eqA : BoolEq A}}  → List A → List A → Bool
φ ⊆ ψ = all (λ x → x ∈b ψ)  φ

_==List_ : {A : Set}{{eqA : BoolEq A}}  → List A → List A → Bool
l ==List l' = (l ⊆ l') ∧b (l' ⊆ l)

length : {X : Set} → List X → ℕ
length [] = zero
length (x ∷ l) = suc (length l)


mapList : {A B : Set}(f : A → B)(l : List A) → List B
mapList f [] = []
mapList f (x ∷ l) = f x ∷ mapList f l

MapListLenCor :  {A B : Set}(f : A → B)(l : List A)
                 → length l ≡ length (mapList f l)
MapListLenCor f [] = refl
MapListLenCor f (x ∷ l) = cong≡ suc (MapListLenCor f l)

MapListLenCor' :  {A B : Set}(f : A → B)(l : List A)
                 →  length (mapList f l) ≡ length l
MapListLenCor' f [] = refl
MapListLenCor' f (x ∷ l) = cong≡ suc (MapListLenCor' f l)


instance
  listEq : {A : Set}{{booleq : BoolEq A}} → BoolEq (List A)
  listEq .eqb = _==List_


mutual
  removeFromList : {A : Set}{{booleq : BoolEq A}} → A → List A → List A
  removeFromList a [] = []
  removeFromList {{booleq}} a (x ∷ l) = removeFromListaux a x l (booleq .eqb a x)

  removeFromListaux : {A : Set}{{booleq : BoolEq A}}
                      (a x : A)(l : List A)(b : Bool) → List A
  removeFromListaux a x l false = x ∷ removeFromList a l
  removeFromListaux a x l true = removeFromList a l

mutual
  addNoDuplicate : {A : Set}{{booleq : BoolEq A}} → A → List A → List A
  addNoDuplicate a [] = a ∷ []
  addNoDuplicate {A} {{booleq}} a (x ∷ l) = addNoDuplicateAux a x l (booleq .eqb a x)

  addNoDuplicateAux : {A : Set}{{booleq : BoolEq A}}(a x : A)(l : List A)
                      (b : Bool) -- (eqb : b ≡ booleq .eqb a x )
                      → List A
  addNoDuplicateAux a x l false = x ∷ (addNoDuplicate a l)
  addNoDuplicateAux a x l true = x ∷ l

{-
_\\_ : {A : Set}{{booleq : BoolEq A}} → List A → A → List A
[] \\ a = []
(a' ∷ l) \\ a with a ==b a'
... | true = l \\ a
... | false = a' ∷ (l \\ a)
-}

mutual
  _\\_ : {A : Set}{{booleq : BoolEq A}} → List A → A → List A
  [] \\ a = []
  (a' ∷ l) \\ a  = setminusAux a' l a (a ==b a')


  setminusAux : {A : Set}{{booleq : BoolEq A}} → A → List A → A →
                Bool → List A
  setminusAux a' l a true   = l \\ a
  setminusAux a' l a false  = a' ∷ (l \\ a)

merge' : {A : Set}{{booleq : BoolEq A}} → List A → List A → List A
merge' [] l' = l'
merge' (a ∷ l) l' = merge' l (addNoDuplicate a l')

nonEmpty : {X : Set} → List X → Bool
nonEmpty [] = false
nonEmpty (_ ∷ _)  = true

-- in Coq result should be Prop
NonEmpty : {X : Set} → List X → Set
NonEmpty l = atom (nonEmpty l)

headNE : {X : Set} (l : List X) → NonEmpty l → X
headNE (x ∷ l) _ = x

nthWithDefault : {X : Set}(n : ℕ)(l : List X) (default : X) → X
nthWithDefault n [] default = default
nthWithDefault zero (x ∷ l) default = x
nthWithDefault (suc n) (x ∷ l) default = nthWithDefault n l default

nthFin : {X : Set}(l : List X) (i : Fin (length l)) → X
nthFin (x ∷ l) zero = x
nthFin (x ∷ l) (suc i) = nthFin l i

nthFinEq : {X : Set}(l : List X){n : ℕ}(p : length l ≡ n)(i : Fin n) → X
nthFinEq l {n} p i =
   let
        i' : Fin (length l)
        i' = transfer≡' Fin (length l) n p i
   in nthFin l i'

nthFinEq' : {X : Set}(l : List X){n : ℕ}(p : n ≡ length l )(i : Fin n) → X
nthFinEq' l {n} p i =
   let
        i' : Fin (length l)
        i' = transfer≡ Fin n (length l) p i
   in nthFin l i'

NthFinEqCor0 : {X : Set}(x : X)(l : List X)(n : ℕ)(p : length (x ∷ l) ≡ suc n)
               → nthFinEq (x ∷ l) p zero ≡ x
NthFinEqCor0 x l .(length l) refl = refl


NthFinEqCorSuc : {X : Set}(x : X)(l : List X)(n : ℕ)(p : length (x ∷ l) ≡ suc n)
               (k : Fin n)

               → nthFinEq (x ∷ l) p (suc k) ≡ nthFinEq l (sucInj p) k
NthFinEqCorSuc x l .(length l) refl k = refl


-- create a list of elements of Fin n, where the kth element is the
-- kth element of Fin n



finList : (n : ℕ) → List (Fin n)
finList 0 = []
finList 1 = zero ∷ []
finList (suc (suc n))  = zero ∷ mapList suc (finList (suc n))

finListLenCor : (n : ℕ) → length (finList n) ≡ n
finListLenCor 0 = refl
finListLenCor 1 = refl
finListLenCor (suc (suc n)) =
      let
           ih : length (finList (suc n)) ≡ suc n
           ih = finListLenCor (suc n)

           p : length (mapList {Fin (suc n)} {Fin (suc (suc n))} suc
               (finList (suc n)))
               ≡ length (finList (suc n))
           p = MapListLenCor' suc (finList (suc n))

           q : length (mapList {Fin (suc n)} {Fin (suc (suc n))} suc
               (finList (suc n)))
               ≡ suc n
           q = trans≡ p ih


      in cong≡ suc q


funToList : {A : Set}{n : ℕ}(f : Fin n → A) → List A
funToList {A}{zero} f = []
funToList {A}{suc n} f = f zero ∷ funToList {A} {n} (λ k → f (suc k))


FunToListLenCor : {A : Set}{n : ℕ}(f : Fin n → A)
                  → length (funToList f) ≡ n
FunToListLenCor {A} {zero} f = refl
FunToListLenCor {A} {suc n} f = cong≡ suc  (FunToListLenCor (λ k → f (suc k)))

FunToListNthCor : {A : Set}{n : ℕ}(f : Fin n → A)(k : Fin n)
                  → nthFinEq (funToList f) (FunToListLenCor f) k
                     ≡ f k
FunToListNthCor f zero = NthFinEqCor0 (f zero)
        (funToList (λ k → f (suc k))) _
        (cong≡ suc (FunToListLenCor (λ k → f (suc k))))
FunToListNthCor f (suc k) =
         let
             p : nthFinEq (f zero ∷ funToList (λ k₁ → f (suc k₁)))
                 (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁)))) (suc k)
                 ≡ nthFinEq  (funToList (λ k₁ → f (suc k₁)))
                             (sucInj (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁))))) k
             p = NthFinEqCorSuc (f zero) (funToList (λ k₁ → f (suc k₁))) _ (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁))))  k

             p' : nthFinEq (f zero ∷ funToList (λ k₁ → f (suc k₁)))
                  (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁)))) (suc k)
                  ≡  nthFinEq  (funToList (λ k₁ → f (suc k₁)))
                    (sucInj (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁))))) k
             p' = p


             q : nthFinEq  (funToList (λ k₁ → f (suc k₁)))
                             (sucInj (cong≡ suc (FunToListLenCor (λ k₁ → f (suc k₁))))) k ≡ nthFinEq  (funToList (λ k₁ → f (suc k₁))) (FunToListLenCor (λ k₁ → f (suc k₁))) k
             q = cong≡ (λ p →  nthFinEq  (funToList (λ k₁ → f (suc k₁))) p  k)  ((sucInjCor (FunToListLenCor (λ k₁ → f (suc k₁)))))

             q' : nthFinEq  (funToList (λ k₁ → f (suc k₁))) (FunToListLenCor (λ k₁ → f (suc k₁))) k ≡ f (suc k)
             q' =  FunToListNthCor (λ k₁ → f (suc k₁)) k
         in trans≡ p' (trans≡ q q')


infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


-- add a to l unless it is already there
mutual
  _∷noDup_ : {A : Set}{{eqA : BoolEq A}}(a : A)(l : List A) → List A
  a ∷noDup l = consNoDupAux a l (a ∈b l)


  consNoDupAux : {A : Set}{{eqA : BoolEq A}}(a : A)(l : List A) → Bool → List A
  consNoDupAux a l false = a ∷ l
  consNoDupAux a l true = l

-- now add a complete list to a list without duplicates
_++noDup_ :  {A : Set}{{eqA : BoolEq A}}(l l' : List A) → List A
[] ++noDup l' = l'
(x ∷ l) ++noDup l' = x ∷noDup (l ++noDup l')


reverseList : {A : Set}  → List A → List A
reverseList [] = []
reverseList (x ∷ l) = reverseList l ++ (x ∷ [])

mapList++ : {A B : Set}(f : A → B)(l l' : List A)
            → mapList f (l ++ l') ≡ mapList f l ++ mapList f l'
mapList++ f [] l' = refl
mapList++ f (x ∷ l) l' = cong≡ (λ y → f x ∷ y) (mapList++ f l l')

assoc++₁ : {A : Set} (l l' l'' : List A) → (l ++ l') ++ l'' ≡ l ++ (l' ++ l'')
assoc++₁ [] l' l'' = refl
assoc++₁ (x ∷ l) l' l'' = cong≡ (λ y → x ∷ y) (assoc++₁ l l' l'')

assoc++₂ : {A : Set} (l l' l'' : List A) → l ++ (l' ++ l'') ≡ (l ++ l') ++ l''
assoc++₂ [] l' l'' = refl
assoc++₂ (x ∷ l) l' l'' = cong≡ (λ y → x ∷ y) (assoc++₂ l l' l'')

++empty : {A : Set}(l : List A) → l ++ [] ≡ l
++empty {A} [] = refl
++empty {A} (x ∷ l) = cong≡ (λ y → x ∷ y) (++empty {A} l)
