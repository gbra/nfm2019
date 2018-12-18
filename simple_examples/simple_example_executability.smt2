; sorts and constants
(declare-const x Int)	; a constant used by transfo 1 and transfo 2
(declare-const y Int)	; a constant used by transfo 3 and transfo 4

; transfo 1
;; postcondition

(declare-const post-transfo1-trigger Bool)

(define-fun post_transfo1 ((var1 Int)) Bool
            (= x var1))

(assert (or (not post-transfo1-trigger)
            (post_transfo1 1)
	)
)

; transfo 2
;; preconditions
(declare-const pre-transfo2-trigger Bool)
(declare-const neg-pre-transfo2-trigger Bool)

(define-fun pre_transfo2 ((var2 Int)) Bool
             (= x var2))

(assert (or (not pre-transfo2-trigger)
            (pre_transfo2 1)
	)
)

(assert (or (not neg-pre-transfo2-trigger)
            (not (pre_transfo2 1))
	)
)

; transfo 3
;; postcondition

(declare-const post-transfo3-trigger Bool)

(define-fun post_transfo3 ((var3 Int)) Bool
            (= y var3))

(assert (or (not post-transfo3-trigger)
            (post_transfo3 2)
	)
)

; transfo 4
;; preconditions
(declare-const pre-transfo4-trigger Bool)
(declare-const neg-pre-transfo4-trigger Bool)

(define-fun pre_transfo4 ((var4 Int)) Bool
             (= y var4))

(assert (or (not pre-transfo4-trigger)
            (pre_transfo4 2)
	)
)

(assert (or (not neg-pre-transfo4-trigger)
            (not (pre_transfo4 2))
	)
)

; checking satisfiability
(echo "checking completeness... (unsat = complete)")
;; triggers to consider all postconditions
(assert (= post-transfo1-trigger true))	; postcondition t1
(assert (= post-transfo3-trigger true))	; postcondition t3

;; triggers to consider preconditions of transfo 2
(push)
(echo "for transfo 2...")
(assert (= pre-transfo2-trigger false))	; precondition t2
(assert (= neg-pre-transfo2-trigger true))	; negation precondition t2
(check-sat)
(pop)

;; triggers to consider preconditions of transfo 4
(push)
(echo "for transfo 4...")
(assert (= pre-transfo4-trigger false))	; precondition t4
(assert (= neg-pre-transfo4-trigger true))	; negation precondition t4
(check-sat)
(pop)
