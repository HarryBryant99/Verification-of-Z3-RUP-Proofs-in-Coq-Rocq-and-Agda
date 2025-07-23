module rup.loadAllRup where

open import rup.clause
open import rup.model
open import rup.preProofsAndChecking
open import rup.preProofsAndCheckingUnused
open import rup.rupChecker
open import rup.rupProof
open import rup.treeProofs
open import rup.uResTreeProofs
open import rup.uResTreeProofsDisplay
open import rup.variablesBasedOnZ3formulas


-- import rup.variablesAbcdefg  -- alternative code, not part of main code
                                -- uses variables for rup checker defined as  a b c d e f g
                                -- We use rup.variablesBasedOnZ3formulas
                                -- instead which uses as rup variables Z3formulas
-- import rup.variablesNat      -- alternative code, not part of main code
                                -- uses variables for rup checker defined as natural numbers
                                -- i.e.  i denoting variable x_i
                                -- We use rup.variablesBasedOnZ3formulas
                                -- instead which uses as rup variables Z3formulas
-- import rup.variablesString   -- alternative code, not part of main code
                                -- uses variables for rup checker defined as strings
                                -- We use rup.variablesBasedOnZ3formulas
                                -- instead which uses as rup variables Z3formulas


open import rup.variablesBasedOnZ3formulas
open import rup.variables
-- open import rup.examplesRupStringVar -- examples, work only if replacing in rup.variables
                                        -- open import rup.variablesBasedOnZ3formulas public
                                        -- by open import rup.variablesString public
-- open import examplesRupABCDEvar -- examples, work only if replacing in rup.variables
                                   -- open import rup.variablesBasedOnZ3formulas public
                                   -- by open import rup.variablesAbcdefg
open import rup.z3BasedClause
open import rup.z3Formulas
open import rup.z3Model
open import rup.z3Proofs
open import rup.z3ProofCorrect
open import rup.z3Variables
