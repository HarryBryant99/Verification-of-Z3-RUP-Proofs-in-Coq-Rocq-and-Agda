(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)

(assert (and (or a b c)  (or  (not a)) (or  (not b))  (or  (not c))))
(check-sat)


