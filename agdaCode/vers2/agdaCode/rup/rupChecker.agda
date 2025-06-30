module rup.rupChecker where

open import lib.boolLib
open import lib.eqLib
open import lib.finLib
open import lib.listLib
open import lib.natLib
open import lib.natLibBase
open import lib.prodLib
open import lib.vecLib

open import rup.variables
open import rup.clause
open import rup.model
open import rup.uResTreeProofs


record Config : Set where
   constructor  config
   field
       nunitCl : RFor
       unitCl  : List RLit

correctConfig : Config → Bool
correctConfig (config nu un) = isNonTrivRClauses nu

-- result if we have processed some a config with one literal
--   but have still more clauses to process
-- success means we have derived unsatisfiability, so RUP succeeds
-- it could be the config is empty, but there might be later
-- clauses still to be added.

data IntermediateOneStepRes : Set where
   continue : Config → IntermediateOneStepRes
   success : IntermediateOneStepRes

-- result if we have finished processing a config with one literal


-- failure means at the end we have clauses which are derivable
--   no unit clauses left, and no [], so checking of rup failed
-- continue means unit propagation carried out continue next step

data FinalRes : Set where
   failure : Config → FinalRes
   continue : Config     → FinalRes
   success : FinalRes

-- continuec means result is a clause of length >= 2
-- continuel means result is a clause of length 1
-- success       means result is [] so we have derived [] success of RUP
-- omit      means contains literal, so can be omitted
data OneStepOneRClauseRes : Set where
    continuec : RClause → OneStepOneRClauseRes
    continuel : RLit → OneStepOneRClauseRes
    omit success : OneStepOneRClauseRes

-- the initial config is a config,
-- or success in case there is a unit clause
-- or failure in case there are no clauses
data InitialConfig : Set where
  success  : InitialConfig
  continue : Config → InitialConfig



mutual
  oneStepOneRClausePropagate : RClause → RLit →  OneStepOneRClauseRes
  oneStepOneRClausePropagate c l = oneStepOneRClausePropagateCheckIn c l (l ∈b c)

  -- same but with b = l ∈b c
  oneStepOneRClausePropagateCheckIn : RClause → RLit →  Bool → OneStepOneRClauseRes
  oneStepOneRClausePropagateCheckIn c l true = omit
  oneStepOneRClausePropagateCheckIn c l false = oneStepOneRClausePropagateCheckNotIn c l ((negRLit l) ∈b c )

  oneStepOneRClausePropagateCheckNotIn : RClause → RLit →  Bool → OneStepOneRClauseRes
  oneStepOneRClausePropagateCheckNotIn [] l false = omit
  oneStepOneRClausePropagateCheckNotIn (l' ∷ [])  l false = continuel l'
  oneStepOneRClausePropagateCheckNotIn cl l false = continuec cl
  oneStepOneRClausePropagateCheckNotIn cl l true = oneStepOneRClausePropagateRClauseCreated (cl \\ (negRLit l))

  oneStepOneRClausePropagateRClauseCreated : RClause → OneStepOneRClauseRes
  oneStepOneRClausePropagateRClauseCreated [] = success
  oneStepOneRClausePropagateRClauseCreated (l ∷ []) = continuel l
  oneStepOneRClausePropagateRClauseCreated c   = continuec c


-- We process all clauses, however after this is done more clauses might
-- need to be processed, so the result is only intermediate

mutual
  oneStepOneConfigPropagateIntermediate : Config → RLit →  IntermediateOneStepRes
  oneStepOneConfigPropagateIntermediate (config (c ∷ cl) ls) l
      = oneStepOneConfigPropagateOneRClause  c l
        (oneStepOneConfigPropagateIntermediate (config cl ls) l)
  oneStepOneConfigPropagateIntermediate (config [] (l' ∷ ls)) l = oneStepOneConfigPropagateOneRClause  (l' ∷ []) l (oneStepOneConfigPropagateIntermediate (config [] ls) l)
  oneStepOneConfigPropagateIntermediate (config [] []) l = continue (config [] [])

  -- we have propagated the remaining configuration
  -- but need to process the last clause
  oneStepOneConfigPropagateOneRClause : (c : RClause)(l : RLit)(ih : IntermediateOneStepRes)
                                       →  IntermediateOneStepRes
  oneStepOneConfigPropagateOneRClause c l (continue cf) = oneStepOneConfigPropagateOneRClauseStep2 cf (oneStepOneRClausePropagate c l)
  oneStepOneConfigPropagateOneRClause c l success = success

{-
  -- we have propagated the remaing configuration, which only contaiend literals
  -- but need to process the remaining clause
  oneStepOneConfigPropagateOneLit : (l' l : RLit)(ih : IntermediateOneStepRes)
                                       →  IntermediateOneStepRes
  oneStepOneConfigPropagateOneLit l' l (continue cf) = oneStepOneConfigPropagateOneRClauseStep2 cf (oneStepOneRClausePropagate (l' ∷ []) l)
  oneStepOneConfigPropagateOneLit l' l success = success
-}

-- we have propagated the remaing configuration
-- and processed the last clause
  oneStepOneConfigPropagateOneRClauseStep2 : (cf : Config) (oneStepRes : OneStepOneRClauseRes)
                                       →  IntermediateOneStepRes
  oneStepOneConfigPropagateOneRClauseStep2 (config nunitCl unitCl) (continuec c₁) = continue (config (c₁ ∷ nunitCl) unitCl)
  oneStepOneConfigPropagateOneRClauseStep2 (config nunitCl unitCl) (continuel l') = continue (config nunitCl (l' ∷ unitCl))
  oneStepOneConfigPropagateOneRClauseStep2 conf omit = continue conf
  oneStepOneConfigPropagateOneRClauseStep2 _ success = success



{-
-- we have propagated the remaing configuration, which only contaiend literals  -- and have processed the last literal
  oneStepOneConfigPropagateOneLitStep2 : (conf : Config)(oneLitRes : OneStepOneRClauseRes)
                                    →  IntermediateOneStepRes
  oneStepOneConfigPropagateOneLitStep2 (config nu un) (continuec c) = continue (config (c ∷ nu) un)
  oneStepOneConfigPropagateOneLitStep2 (config nu un) (continuel l'') = continue (config nu (l'' ∷ un))
  oneStepOneConfigPropagateOneLitStep2 conf omit = continue conf
  oneStepOneConfigPropagateOneLitStep2 conf success = success
-}


-- we convert the intermediate result which is
--  either success i.e. [] is derivable
--  or a configuration
--  to the final result:
--  where if we have no literals left then we get a failure
--  we cannot derive []
intermediateOneStep2FinalStep : IntermediateOneStepRes → FinalRes
intermediateOneStep2FinalStep (continue (config nunitCl [])) = failure (config nunitCl [])
intermediateOneStep2FinalStep (continue conf) = continue conf
intermediateOneStep2FinalStep success = success

oneStepOneConfigPropagateFinal : Config → FinalRes
oneStepOneConfigPropagateFinal (config nunitCl []) = failure (config nunitCl [])
oneStepOneConfigPropagateFinal (config nunitCl (l ∷ ls)) = intermediateOneStep2FinalStep (oneStepOneConfigPropagateIntermediate (config nunitCl ls) l)

mutual
  nStepsConfigPropagateFinal : Config → ℕ → FinalRes
  nStepsConfigPropagateFinal (config nunitCl unitCl) zero = failure (config nunitCl unitCl)
  nStepsConfigPropagateFinal cf (suc n) = nStepsConfigPropagateFinalaux (oneStepOneConfigPropagateFinal cf) n

  nStepsConfigPropagateFinalaux : FinalRes → ℕ → FinalRes
  nStepsConfigPropagateFinalaux (failure c) n = failure c
  nStepsConfigPropagateFinalaux (continue cf) n = nStepsConfigPropagateFinal cf n
  nStepsConfigPropagateFinalaux success n = success

mutual
  initialConfig : RFor → InitialConfig
  initialConfig [] = continue (config [] [])
  initialConfig (c ∷ cl) = initialConfigAux c (initialConfig cl)

  -- processing one clause of lenth n
  initialConfigAux : RClause → InitialConfig → InitialConfig
  initialConfigAux [] cl = success
  initialConfigAux c success = success
  initialConfigAux (l ∷ []) (continue (config nCl uCl)) =
                      continue (config nCl (l ∷ uCl))
  initialConfigAux c (continue (config nCl uCl)) = continue (config (c ∷ nCl) uCl)

-- takes an assuption and rupfor and creates the clauses
-- consisting of the assumption and unit clauses for each negated literal in
-- the rupfor
createFullRupRClause : (as : RFor)(rupfor : RClause) → RFor
createFullRupRClause as ls = (lits2RClauses (negRLits (reverseList ls))) ++ as


nStepsInitialConfigPropagateFinal : InitialConfig → ℕ → FinalRes
nStepsInitialConfigPropagateFinal success n = success
nStepsInitialConfigPropagateFinal (continue cl) n = nStepsConfigPropagateFinal cl n

checkOneRupWithInfo : RFor → RClause → FinalRes
checkOneRupWithInfo as rp =
  let
      cl' : RFor
      cl' = createFullRupRClause as rp

      n : ℕ
      n = #varsInRClauses cl'

      inConfig : InitialConfig
      inConfig = initialConfig cl'
  in nStepsInitialConfigPropagateFinal inConfig n

finalRes2Bool : FinalRes → Bool
finalRes2Bool success = true
finalRes2Bool _  = false



checkOneRup : RFor → RClause → Bool
checkOneRup f c = finalRes2Bool (checkOneRupWithInfo f c)


RupProof : Set
RupProof = List RClause

rupProof : RFor → RupProof → Bool
rupProof f [] = true
rupProof f (r ∷ rp) = (checkOneRup f r) ∧b rupProof (r ∷ f) rp

rupProofOfUnSat  : RFor → RupProof → Bool
rupProofOfUnSat  f rp = rupProof f rp ∧b ([] ∈b rp)
