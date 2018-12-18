; sorts and constants
(declare-const x Int)	; a constant used by transfo 1 and transfo 2
(declare-const y Int)	; a constant used by transfo 3
(declare-const z Int)	; a constant used by transfo 4

; transfo 1
;; postcondition

(declare-const post-transfo1-trigger Bool)
(declare-const neg-post-transfo1-trigger Bool)

(define-fun post_transfo1 ((var1 Int)) Bool
            (= x var1))

(assert (or (not post-transfo1-trigger)
            (post_transfo1 1)
	)
)

(assert (or (not neg-post-transfo1-trigger)
            (not (post_transfo1 1))
	)
)

; transfo 2
;; postcondition
(declare-const post-transfo2-trigger Bool)
(declare-const neg-post-transfo2-trigger Bool)

(define-fun post_transfo2 ((var2 Int)) Bool
            (= x var2))

(assert (or (not post-transfo2-trigger)
            (post_transfo2 1)
	)
)

(assert (or (not neg-post-transfo2-trigger)
            (not (post_transfo2 1))
	)
)

; transfo 3
;; postcondition

(declare-const post-transfo3-trigger Bool)
(declare-const neg-post-transfo3-trigger Bool)

(define-fun post_transfo3 ((var3 Int)) Bool
            (= y var3))

(assert (or (not post-transfo3-trigger)
            (post_transfo3 2)
	)
)

(assert (or (not neg-post-transfo3-trigger)
            (not (post_transfo3 2))
	)
)

; transfo 4
;; postcondition

(declare-const post-transfo4-trigger Bool)
(declare-const neg-post-transfo4-trigger Bool)

(define-fun post_transfo4 ((var4 Int)) Bool
            (= z var4))

(assert (or (not post-transfo4-trigger)
            (post_transfo4 2)
	)
)

(assert (or (not neg-post-transfo4-trigger)
            (not (post_transfo4 2))
	)
)

; checking satisfiability
(echo "checking redundancy... (unsat = redundancy)")

; for transfo 1
(push)
(echo "for transfo 1...")
(assert (= neg-post-transfo1-trigger true))	
(assert (= post-transfo2-trigger true))	
(assert (= post-transfo3-trigger true))	
(assert (= post-transfo4-trigger true))	
(check-sat)
(pop)

; for transfo 2
(push)
(echo "for transfo 2...")
(assert (= post-transfo1-trigger true))	
(assert (= neg-post-transfo2-trigger true))	
(assert (= post-transfo3-trigger true))	
(assert (= post-transfo4-trigger true))
(check-sat)
(pop)

; for transfo 3
(push)
(echo "for transfo 3...")
(assert (= post-transfo1-trigger true))	
(assert (= post-transfo2-trigger true))	
(assert (= neg-post-transfo3-trigger true))	
(assert (= post-transfo4-trigger true))
(check-sat)
(pop)

; for transfo 4
(push)
(echo "for transfo 4...")
(assert (= post-transfo1-trigger true))	
(assert (= post-transfo2-trigger true))	
(assert (= post-transfo3-trigger true))	
(assert (= neg-post-transfo4-trigger true))
(check-sat)
(pop)
