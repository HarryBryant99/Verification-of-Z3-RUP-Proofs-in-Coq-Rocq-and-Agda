module  rup.z3BasedClause where

open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny

open import rup.z3Variables
open import rup.z3Formulas
open import rup.clause


Zfor2Lit : ZFor → RLit
-- formula2RLit (notFor (notFor x)) = formula2RLit x
Zfor2Lit (notFor x) = negRLit (Zfor2Lit x)
Zfor2Lit x  = pos x

{-
test1 : RLit
test1 =  Zfor2Lit (notFor (notFor (zvar "x")))

test2 : RLit
test2 =  Zfor2Lit (notFor (notFor (notFor (zvar "x"))))
-}

zCl2RClause : ZClause → RClause
zCl2RClause [] = []
zCl2RClause (x ∷ l) = Zfor2Lit x ∷ zCl2RClause l

zListCl2RListCl : List  ZClause → List RClause
zListCl2RListCl [] = []
zListCl2RListCl (x ∷ l) = zCl2RClause x ∷ zListCl2RListCl l
