(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(declare-const f Bool)
(declare-const g Bool)
(declare-const h Bool)

(assert (or (not a) b))
(assert (or (not b) c))
(assert (or (not c) d))
(assert (or (not d) (not a)))
(assert (or a b))
(assert (or (not d) a))

(check-sat)


