; sorts and constants
(declare-const x Int)	; a constant used by transfo 1 
(declare-const y Int)	; a constant used by transfo 2
(declare-const z Int)	; a constant used by transfo 3 and 4

; transfo 1
;; precondition

(declare-const pre-transfo1-trigger Bool)
(declare-const neg-pre-transfo1-trigger Bool)

(define-fun pre_transfo1 ((var1 Int)) Bool
            (= x var1))

(assert (or (not pre-transfo1-trigger)
            (pre_transfo1 1)
	)
)

(assert (or (not neg-pre-transfo1-trigger)
            (not (pre_transfo1 1))
	)
)

; transfo 2
;; precondition
(declare-const pre-transfo2-trigger Bool)
(declare-const neg-pre-transfo2-trigger Bool)

(define-fun pre_transfo2 ((var2 Int)) Bool
            (= y var2))

(assert (or (not pre-transfo2-trigger)
            (pre_transfo2 1)
	)
)

(assert (or (not neg-pre-transfo2-trigger)
            (not (pre_transfo2 1))
	)
)

; transfo 3
;; precondition

(declare-const pre-transfo3-trigger Bool)
(declare-const neg-pre-transfo3-trigger Bool)

(define-fun pre_transfo3 ((var3 Int)) Bool
            (= z var3))

(assert (or (not pre-transfo3-trigger)
            (pre_transfo3 2)
	)
)

(assert (or (not neg-pre-transfo3-trigger)
            (not (pre_transfo3 2))
	)
)

; transfo 4
;; precondition

(declare-const pre-transfo4-trigger Bool)
(declare-const neg-pre-transfo4-trigger Bool)

(define-fun pre_transfo4 ((var4 Int)) Bool
            (= z var4))

(assert (or (not pre-transfo4-trigger)
            (pre_transfo4 2)
	)
)

(assert (or (not neg-pre-transfo4-trigger)
            (not (pre_transfo4 2))
	)
)

; checking satisfiability
(echo "checking determinism... (unsat = redundant input)")

; for transfo 1
(push)
(echo "for transfo 1...")
(assert (= neg-pre-transfo1-trigger true))	
(assert (= pre-transfo2-trigger true))	
(assert (= pre-transfo3-trigger true))	
(assert (= pre-transfo4-trigger true))	
(check-sat)
(pop)

; for transfo 2
(push)
(echo "for transfo 2...")
(assert (= pre-transfo1-trigger true))	
(assert (= neg-pre-transfo2-trigger true))	
(assert (= pre-transfo3-trigger true))	
(assert (= pre-transfo4-trigger true))
(check-sat)
(pop)

; for transfo 3
(push)
(echo "for transfo 3...")
(assert (= pre-transfo1-trigger true))	
(assert (= pre-transfo2-trigger true))	
(assert (= neg-pre-transfo3-trigger true))	
(assert (= pre-transfo4-trigger true))
(check-sat)
(pop)

; for transfo 4
(push)
(echo "for transfo 4...")
(assert (= pre-transfo1-trigger true))	
(assert (= pre-transfo2-trigger true))	
(assert (= pre-transfo3-trigger true))	
(assert (= neg-pre-transfo4-trigger true))
(check-sat)
(pop)
