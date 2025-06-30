module rup.variablesBasedOnZ3formulas where

open import Data.String
open import lib.stringLib
open import lib.boolLib
open import lib.eqLib
open import rup.z3Formulas

RVar : Set
RVar = ZFor

_==RVar_ : RVar → RVar → Bool
_==RVar_ = _==ZFor_

eqRVarTo== : (a b : RVar) → atom (a ==RVar b) → a ≡ b
eqRVarTo== = eqZFor2≡
