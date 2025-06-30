
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

