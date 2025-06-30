module rup.preProofsAndChecking where


data List (X : Set) : Set where
   [] : List X
   _∷_ : X → List X → List X

data Bool : Set where
   true false : Bool

_∧b_ : Bool → Bool → Bool
true ∧b b = b
false ∧b _ = false

nonEmpty : {X : Set} → List X → Bool
nonEmpty [] = false
nonEmpty (_ ∷ _)  = true


record _∧_ (A B : Set) : Set where
  constructor _andp_
  field
     fst : A
     snd : B
open _∧_ public

-- false formula
data ⊥ : Set where


-- true formula having proof tt
record ⊤ : Set where
  constructor tt
open ⊤ public

-- atom converts
--    true into the true formula
--    false into the false formula
-- In Coq the result would probably be Prop
atom : Bool → Set
atom true = ⊤
atom false = ⊥

-- in Coq result should be Prop
NonEmpty : {X : Set} → List X → Set
NonEmpty l = atom (nonEmpty l)

head : {X : Set} (l : List X) → NonEmpty l → X
head (x ∷ l) _ = x

∧b-elim1 : (b1 b2 : Bool) → atom (b1 ∧b b2) → atom b1
∧b-elim1 true b2 p = tt

∧b-elim2 : (b1 b2 : Bool) → atom (b1 ∧b b2) → atom b2
∧b-elim2 true true _ = tt

∧b-to-∧ : {b1 b2 : Bool} → atom (b1 ∧b b2) → atom b1 ∧ atom b2
∧b-to-∧  {true} {true} _ = tt andp tt

∧b3-to-∧ : {b1 b2 b3 : Bool} → atom (b1 ∧b (b2 ∧b b3)) → atom b1 ∧ (atom b2 ∧ atom b3)
∧b3-to-∧ {true} {true} {true} _ =  tt andp (tt andp tt)


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

length : {X : Set} → List X → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

-- nthWithDefault n l default
-- returns    the nth element of l   if n < length l
--            default                if n >= length l


nthWithDefault : {X : Set}(n : ℕ)(l : List X) (default : X) → X
nthWithDefault n [] default = default
nthWithDefault zero (x ∷ l) default = x
nthWithDefault (suc n) (x ∷ l) default = nthWithDefault n l default

_<b_ : ℕ → ℕ → Bool
_     <b zero    = false
zero  <b (suc _) = true
suc n <b suc m   = n <b m

-- In Coq result probably Prop
_<_ : ℕ → ℕ → Set
n < m = atom ( n <b m)



postulate Clause : Set

{-
 IsRes c1 c2 should check whether  having the two claauses is a valid resolution step
 i.e.
 whether
   c1 and c2 are assumptions of a resolution proof with a conclusion c3

          c1   c2
          --------
            c3
-}

--  trueClause should be a clause which is true
postulate trueClause : Clause

postulate isRes : Clause → Clause → Bool

-- In Coq result Prop
IsRes : Clause → Clause → Set
IsRes c1 c2 = atom (isRes c1 c2)

{-
toResConclusion c1 c2 computes the result of a resolution proof which conclusions
   c1
 i.e.
 it computes if we have a resoulution proof step

          c1    c2
          ---------
             c3

the c3 from c1 and c2

if it is not correct it returns the trueClause
-}

postulate toResConclusion : Clause → Clause → Clause

-- isEmptyClause should return true if it is the empty i.e. false clause
postulate isEmptyClause : Clause → Bool

-- result should be Prop
IsEmptyClause : Clause → Set
IsEmptyClause c = atom (isEmptyClause c)


data PreProofStep : Set  where
       ass : (n : ℕ) → PreProofStep
       res : (n m : ℕ) → PreProofStep

PreProof : Set
PreProof = List PreProofStep


-- nthElInSeq computes the nth element of a list of clauses (a sequence)
--   if there n is too bit it computes the trueClause
nthElInSeq : ℕ → (ass : List Clause) → Clause
nthElInSeq n as = nthWithDefault n as trueClause


mutual
   -- lastConclusion as p pl  computes the last conclusion of a  preproof (p ∷ pl)
   lastConclusion : (as : List Clause)(p : PreProofStep)(pl :  PreProof) → Clause
   lastConclusion as (ass n) pl = nthElInSeq n as
   lastConclusion as (res n m) pl =
      let
        conclusionl : List Clause
        conclusionl = conclusions as pl
      in   toResConclusion (nthElInSeq n conclusionl) (nthElInSeq m conclusionl)

   conclusions : (as : List Clause) → PreProof → List Clause
   conclusions as [] = []
   conclusions as (p ∷ pl)  = lastConclusion as p pl  ∷ conclusions as pl

   -- isCorrectLastStep as p pl  checks whether the last step of the proof
   -- (p ∷ pl) is correct
   isCorrectLastStep : (as : List Clause)(p : PreProofStep)(pl :  PreProof) → Bool
   isCorrectLastStep as (ass n) pl = n <b length as
   isCorrectLastStep as (res n m) pl = let
        conclusionpl : List Clause
        conclusionpl = conclusions as pl

        lengthConcll : ℕ
        lengthConcll = length conclusionpl
     in  (n <b lengthConcll) ∧b
          ((m <b lengthConcll) ∧b
           (isRes (nthElInSeq n conclusionpl) (nthElInSeq m conclusionpl)))



   isCorrect : (as : List Clause) → PreProof → Bool
   isCorrect as [] = true
   isCorrect as (p ∷ l) =  isCorrectLastStep as p l ∧b isCorrect as l

    -- we could define
    -- IsCorrect as p = atom (isCorrect as p)
    -- but then unpacking of the conjunctions is tedious
    -- instead we define IsCorrect separately and then proof that
    --  atom (isCorrect as p) implies IsCorrect as p

   -- in Coq result Prop
   IsCorrectLastStep : (as : List Clause)(p : PreProofStep)(pl :  PreProof) → Set
   IsCorrectLastStep as (ass n) pl = n < length as
   IsCorrectLastStep as (res n m) pl = let
        conclusionpl : List Clause
        conclusionpl = conclusions as pl

        lengthConcll : ℕ
        lengthConcll = length conclusionpl
     in  (n < lengthConcll) ∧
          ((m < lengthConcll) ∧
           (IsRes (nthElInSeq n conclusionpl) (nthElInSeq m conclusionpl)))

   -- in Coq result Prop
   IsCorrect : (as : List Clause) → PreProof → Set
   IsCorrect as [] = ⊤
   IsCorrect as (p ∷ l) =  IsCorrectLastStep as p l ∧ IsCorrect as l

-- in Coq result Prop
IsCorrectLastStep' : (as : List Clause) → PreProofStep → PreProof → Set
IsCorrectLastStep' as p pl = atom (isCorrectLastStep as p pl)

IsCorrect' : (as : List Clause) → PreProof → Set
IsCorrect' as p = atom (isCorrect as p)


mutual
  isCorrect'ToIsCorrectLastStep : (as : List Clause)(p : PreProofStep)
                          (pl : PreProof) →
                          IsCorrectLastStep' as p pl → IsCorrectLastStep as p pl
  isCorrect'ToIsCorrectLastStep as (ass n) pl c = c
  isCorrect'ToIsCorrectLastStep as (res n m) pl c = ∧b3-to-∧ c

  isCorrect'ToIsCorrect : (as : List Clause) → (p : PreProof) →
                          IsCorrect' as p → IsCorrect as p
  isCorrect'ToIsCorrect as [] c = tt
  isCorrect'ToIsCorrect as (p ∷ pl) c =
     let
         q :  IsCorrectLastStep' as p pl ∧ IsCorrect' as pl
         q = ∧b-to-∧ c
     in isCorrect'ToIsCorrectLastStep as p pl (q .fst)
        andp isCorrect'ToIsCorrect as pl (q .snd)


{-

lemmaIsCorrectTail : (as : List Clause)(p1 : PreProofStep)(p2 : PreProof)
                     → IsCorrect as (p1 ∷ p2)
                     → IsCorrect as p2
lemmaIsCorrectTail as (ass n) p2 q = q .snd
lemmaIsCorrectTail as (res n m) p2 q = q .snd .snd .snd
-}



-- In Coq result would be Prop
postulate _entails_ : List Clause → Clause → Set


-- In Coq result would be Prop
_entailsl_ : List Clause → List Clause → Set
l entailsl  [] = ⊤
l entailsl  (c ∷ t) = (l entails c) ∧ (l entailsl t)



-- In Coq result should be Prop
postulate Unsatisfiable : List Clause → Set

-- if a clause entails the empty clause it shoud be unsatisfiable
postulate entails⊥-unsat : (as : List Clause)(c : Clause) → as entails c
                           → IsEmptyClause c
                           → Unsatisfiable as




-- the nth element of a clause is entailed from a clause
--  should be true even for the default element since we use the true clause
postulate  assCor :   (n : ℕ) (as : List Clause) → as  entails (nthElInSeq n as)


-- If we have a resolution step of proofs which conclusion c1 and c2
--  and the assumptions are entail c1 and c2 then they entail as well the conclusion

postulate  resCor : (as : List Clause) (c1 c2 : Clause)
                    →  (en1 : as entails c1)
                    →  (en2 : as entails c2)
                    →  IsRes c1 c2
                    → as entails  (toResConclusion c1 c2)

postulate trueentailed : {as : List Clause} → as entails trueClause

entailslToNth : (as : List Clause)(cl : List Clause)(n : ℕ)
                → as entailsl cl
                → as entails (nthElInSeq n cl)
entailslToNth as [] n p = trueentailed
entailslToNth as (x ∷ cl) zero p = p .fst
entailslToNth as (x ∷ cl) (suc n) p = entailslToNth as cl n (p .snd)



lemPreProofEntails : (as : List Clause)(p : PreProof)
                      (cor : IsCorrect as p)
                      → as entailsl  (conclusions as p)
lemPreProofEntails as [] cor = tt
lemPreProofEntails as (p ∷ pl) cor .snd = lemPreProofEntails as pl (cor .snd)
lemPreProofEntails as (ass n ∷ p) cor .fst = assCor n as
lemPreProofEntails as (res n m ∷ p) cor .fst =
         resCor as (nthElInSeq n (conclusions as p)) (nthElInSeq m (conclusions as p))
                (entailslToNth as (conclusions as p) n
                 (lemPreProofEntails as p (cor .snd )))
                (entailslToNth as (conclusions as p) m
                 (lemPreProofEntails as p (cor .snd )))
                (cor .fst .snd .snd)


{- FIRST MAIN THEOREM -}


-- The correctness of the "isCorrect" function is expressed by the following theorem
--   (the previous lemma proofs if for IsCorrect which is in Coq a Prop
--   whereas isCorrect we can extract directly

theoPreProofEntails : (as : List Clause)(p : PreProof)
                      (cor : atom (isCorrect as p))
                      → as entailsl  (conclusions as p)
theoPreProofEntails as p cor =  lemPreProofEntails as p
                                     (isCorrect'ToIsCorrect as p cor)


-- Now we deal with proper resolution proofs, i.e. proofs with conclusion the empty
-- i.e. false clause

-- We need to work with nonempty proofs


data PreProofNonEmpty : Set  where
  single : PreProofStep → PreProofNonEmpty
  cons   : PreProofStep → PreProofNonEmpty → PreProofNonEmpty


preProofNonEmpty2PreProof : PreProofNonEmpty → PreProof
preProofNonEmpty2PreProof (single p ) = p ∷ []
preProofNonEmpty2PreProof (cons p pl) = p ∷ preProofNonEmpty2PreProof pl

isNonEmpty : (p : PreProofNonEmpty) → NonEmpty (preProofNonEmpty2PreProof p)
isNonEmpty (single x) = tt
isNonEmpty (cons x p) = tt



conclusionNonempty : (as : List Clause)(p : PreProof) → NonEmpty p → NonEmpty (conclusions as p)
conclusionNonempty as (x ∷ p) ne = tt


toConclusion' : (as : List Clause)(p : PreProof) → NonEmpty p
               → Clause
toConclusion' as p ne = head (conclusions as p) (conclusionNonempty as p ne)


toConclusion : (as : List Clause)(p : PreProofNonEmpty)
               → Clause
toConclusion as p = toConclusion' as (preProofNonEmpty2PreProof p) (isNonEmpty p)


entailsConclusionaux : (as : List Clause)(p : PreProof)(ne : NonEmpty p)
                     → as entailsl (conclusions as p)
                     → as entails toConclusion' as p ne
entailsConclusionaux as (x ∷ p) ne ent = ent .fst

entailsConclusionaux' : (as : List Clause)(p : PreProofNonEmpty)
                     → as entailsl (conclusions as (preProofNonEmpty2PreProof p))
                     → as entails toConclusion as p
entailsConclusionaux' as p c  = entailsConclusionaux  as (preProofNonEmpty2PreProof p) (isNonEmpty p) c

lemEntailsConclusion' : (as : List Clause)(p : PreProofNonEmpty)
                        → atom (isCorrect as (preProofNonEmpty2PreProof p))
                        → as entails toConclusion as p
lemEntailsConclusion' as p c = entailsConclusionaux' as p
                      (lemPreProofEntails as (preProofNonEmpty2PreProof p)
                        (isCorrect'ToIsCorrect as (preProofNonEmpty2PreProof p) c))


-- isUnsatProof as p ne  checks whether p is a correct proof with false conclusion
--  i.e. a proper resolution proof
isUnsatProof'' : (as : List Clause) (p : PreProof) (ne : NonEmpty p) → Set
isUnsatProof'' as p ne = atom (isCorrect as p) ∧ IsEmptyClause (toConclusion' as p ne)

isUnsatProof' : (as : List Clause) (p : PreProof) (ne : NonEmpty p) → Bool
isUnsatProof' as p ne = isCorrect as p ∧b isEmptyClause (toConclusion' as p ne)

isUnsatProof : (as : List Clause) (p : PreProofNonEmpty) → Bool
isUnsatProof as p = isUnsatProof' as (preProofNonEmpty2PreProof p) (isNonEmpty p)

unsatProof2UnsatProof'' : (as : List Clause) (p : PreProofNonEmpty)
                         → atom (isUnsatProof as p)
                         → isUnsatProof'' as (preProofNonEmpty2PreProof p) (isNonEmpty p)
unsatProof2UnsatProof'' as p c = ∧b-to-∧ c

unsatProof2correct : (as : List Clause) (p : PreProofNonEmpty) → atom (isUnsatProof as p )
                     → atom (isCorrect as (preProofNonEmpty2PreProof p))
unsatProof2correct as p c = unsatProof2UnsatProof'' as p c .fst

unsatProof2proof'' : (as : List Clause)(p : PreProofNonEmpty)
                     → atom (isUnsatProof as p)
                     → isUnsatProof'' as (preProofNonEmpty2PreProof p) (isNonEmpty p)
unsatProof2proof''  as p q = ∧b-to-∧ q

unsatProof2Entails : (as : List Clause)(p : PreProofNonEmpty)
                     → atom (isUnsatProof as p)
                     → as entails toConclusion as p
unsatProof2Entails as p c = lemEntailsConclusion' as p (unsatProof2correct as p c)


unsatProof2IsEmpty : (as : List Clause) (p : PreProofNonEmpty)
                     → atom (isUnsatProof as p )
                     → IsEmptyClause (toConclusion as p)
unsatProof2IsEmpty as p c = unsatProof2UnsatProof'' as p c .snd


{- THEOREM 2  - a resolution proof concluding the empty clause implies
               that the assumptions are unsatisfiable  -}


theoUnsat : (as : List Clause) (p : PreProofNonEmpty)
            → atom (isUnsatProof as p )
            → Unsatisfiable as
theoUnsat as p c = entails⊥-unsat as (toConclusion as p)
                   (unsatProof2Entails as p c)
                   (unsatProof2IsEmpty as p c)
