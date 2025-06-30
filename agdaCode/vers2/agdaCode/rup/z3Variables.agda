module rup.z3Variables where

open import Data.String
open import lib.boolLib
open import lib.natLibBase
open import lib.natLib
open import lib.eqLib
open import lib.listLib
open import lib.listLibAny
open import lib.stringLib



ZVar : Set
ZVar = String

_==zVar_ : ZVar → ZVar → Bool
_==zVar_ =  _==str_

eqZVarTo== : (n m : ZVar) → atom (n ==zVar m) → n ≡ m
eqZVarTo== = ==strTo≡
