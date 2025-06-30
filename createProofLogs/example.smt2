; Without the first 3 comment out lines one can run
; z3 anton_tseitin.smt2 sat.euf=true tactic.default_tactic=smt solver.proof.log=anton_prooflogaux.smt2
; to create the intermediate prooflog
;
; If they are uncommented they override the parameters from the z3 command above and you can run
; z3 anton_tseitin.smt2
; (and if you had parameters they would be overriden)


;
;(set-option :sat.euf true)
;(set-option :tactic.default_tactic smt)
;(set-option :solver.proof.log anton.smt2)

;;(set-logic QF_BOOL)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)

(assert
  (and
    (or
      (and
        (=> x y)
        (=> y x)
        x
        (not y)
      )
      z
    )
    (not z)
  )
)

(check-sat)

