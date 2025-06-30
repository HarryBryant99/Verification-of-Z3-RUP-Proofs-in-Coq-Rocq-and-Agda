module rup.treeProofs where

open import lib.boolLib
open import lib.eqLib
open import lib.finLib
open import lib.listLib
open import lib.natLib
open import lib.prodLib
open import lib.vecLib

open import rup.variables
open import rup.clause

data TreeProof (as : List RClause) : Set where
  ass : Fin (length as) → TreeProof as
  res : (t1 t2 : TreeProof as) → RLit → TreeProof as


conclusion : (as : List RClause) → TreeProof as → RClause
conclusion as (ass i)       = nthFin as i
conclusion as (res t1 t2 l) =  mergeCl ((conclusion as t1) \\ (negRLit l))
                                       ((conclusion as t2) \\ l)
