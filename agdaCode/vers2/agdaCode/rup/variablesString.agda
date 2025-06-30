module rup.variablesString where

open import Data.String
open import lib.stringLib
open import lib.boolLib
open import lib.eqLib

RVar : Set
RVar = String

_==RVar_ : RVar → RVar → Bool
_==RVar_ = _==str_

eqRVarTo== : (a b : RVar) → atom (a ==RVar b) → a ≡ b
eqRVarTo== = ==strTo≡
