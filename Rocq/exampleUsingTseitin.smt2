(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)

(assert (and (or (and a b c d) (and a b c (not d))) (not a)))
(check-sat)

