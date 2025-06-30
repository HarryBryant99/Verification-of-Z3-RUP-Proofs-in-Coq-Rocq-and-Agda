(set-option :sat.euf true)
(set-option :tactic.default_tactic smt)
(set-option :solver.proof.log rhdr_romney_sands.smt2)

;; Define signals for the tracks
(declare-fun s0 () Bool)  ; Signal for A to B
(declare-fun s1 () Bool)  ; Signal for B to A
(declare-fun s2 () Bool)  ; Signal for C to B
(declare-fun s3 () Bool)  ; Signal for B to C

;; Define tracks and loops
(declare-fun track_NR () Bool)  ; Track between A and B
(declare-fun track_RD () Bool)  ; Track between B and C
(declare-fun loop_track_1 () Bool) ; Loop track 1 at B
(declare-fun loop_track_2 () Bool) ; Loop track 2 at B

;; Define points at each end of the loop
(declare-fun p0 () Bool)  ; Point 1 for the loop track
(declare-fun p1 () Bool)  ; Point 2 for the loop track

;; Conditions for signals
(assert (= s0 (and (not s1)    ; S0 must be red
                    p0)))      ; Point 0 must be normal

(assert (= s1 (and (not s0)    ; S1 must be red
                   (not p0)))) ; Point 0 must be reversed

(assert (= s2 (and (not s3)    ; S3 must be red
                    p1)))      ; Point 1 must be normal

(assert (= s3 (and (not s2)    ; S2 must be red
                   (not p1)))) ; Point 2 must be reversed

;; Create conditions that lead to a contradiction
;; Let's assume both pairs of signals are green at the same time
;(assert (and s0 s1))  ; Assume signal N is green AND signal R is green
;(assert (and s3 s2))  ; Assume signal S is green AND signal D is green
(assert (or (and s0 s1) (and s2 s3)))

;; Check satisfiability
(check-sat)
