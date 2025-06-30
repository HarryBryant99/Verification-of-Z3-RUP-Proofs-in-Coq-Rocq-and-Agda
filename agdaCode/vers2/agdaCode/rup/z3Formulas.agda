module rup.z3Formulas where


open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny

open import rup.z3Variables

-- Formulas for Z3 proof input
-- for instance impFor is only binary whereas in the prover
-- we have implications with more then one premises which in the proof format
-- is translated into binary implications so
--  (=> x y z) becomes (=> x (=> y z))
data ZFor : Set where
  zvar : ZVar → ZFor
  andFor : List ZFor → ZFor
  orFor : List ZFor → ZFor
  impFor : ZFor → ZFor → ZFor
  notFor    : ZFor → ZFor
  trueFor   : ZFor
  falseFor   : ZFor


ZClause : Set
ZClause = List ZFor

negFor : ZFor → ZFor
negFor (notFor x) = x
negFor trueFor = falseFor
negFor falseFor = trueFor
negFor x = notFor x

negForList : List ZFor → List ZFor
negForList [] = []
negForList (a ∷ l) = negFor a ∷ negForList l

mutual
   _==ZFor_ : ZFor → ZFor → Bool
   zvar x ==ZFor zvar y = x  ==zVar y
   andFor l ==ZFor andFor l' = l ==ZForl l'
   orFor l ==ZFor orFor l' = l ==ZForl l'
   impFor a b ==ZFor impFor a' b' = (a ==ZFor a') ∧b (b ==ZFor b')
   notFor a ==ZFor notFor a' = a ==ZFor a'
   trueFor ==ZFor trueFor = true
   falseFor ==ZFor falseFor = true
   _ ==ZFor _ = false

   _==ZForl_ : List ZFor → List ZFor → Bool
   [] ==ZForl [] = true
   (a ∷ l) ==ZForl (b ∷ l') = (a ==ZFor b) ∧b  (l ==ZForl l')
   _ ==ZForl _ = false

mutual
  eqZFor2≡  : (l l' : ZFor) → atom (l ==ZFor l') → l ≡ l'
  eqZFor2≡ (zvar x) (zvar y) p = cong≡ zvar (eqZVarTo== x y p)
  eqZFor2≡ (andFor l) (andFor l') p = cong≡ andFor (eqZlFor2≡  l l' p)
  eqZFor2≡ (orFor l) (orFor l') p = cong≡ orFor (eqZlFor2≡  l l' p)
  eqZFor2≡ (impFor a b) (impFor a' b') p =
     let
       aa'b : T (a ==ZFor a')
       aa'b = ∧b-elim1 (a ==ZFor a') (b ==ZFor b') p

       bb'b : T (b ==ZFor b')
       bb'b = ∧b-elim2 (a ==ZFor a') (b ==ZFor b') p

       aa' : a ≡ a'
       aa' = eqZFor2≡ a a' aa'b

       bb' : b ≡ b'
       bb' = eqZFor2≡ b b' bb'b


     in doubleCong≡ impFor aa' bb'
  eqZFor2≡ (notFor a) (notFor b) p = cong≡ notFor (eqZFor2≡  a b p)
  eqZFor2≡ trueFor trueFor p = refl
  eqZFor2≡ falseFor falseFor p = refl

  eqZlFor2≡  : (l l' : List ZFor) → atom (l ==ZForl l') → l ≡ l'
  eqZlFor2≡ [] [] p = refl
  eqZlFor2≡ (x ∷ l) (y ∷ l') p =
     let
       xyb : T (x ==ZFor y)
       xyb = ∧b-elim1 (x ==ZFor y) (l ==ZForl l') p

       ll'b : T (l ==ZForl l')
       ll'b = ∧b-elim2 (x ==ZFor y) (l ==ZForl l') p

       xy : x ≡ y
       xy = eqZFor2≡ x y xyb

       ll' : l ≡ l'
       ll' = eqZlFor2≡ l l' ll'b


     in doubleCong≡ _∷_  xy ll'


containsEmpty : List (List ZFor) → Bool
containsEmpty [] = false
containsEmpty ([] ∷ l) = true
containsEmpty ((a ∷ c) ∷ l) = containsEmpty l

ContainsEmpty : List(List ZFor) → Set
ContainsEmpty l = atom (containsEmpty l)
