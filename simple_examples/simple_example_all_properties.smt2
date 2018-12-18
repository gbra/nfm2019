(set-info :smt-lib-version 2.6)
(set-option :produce-unsat-cores true)

; sorts and constants
(declare-const x Int)	
(declare-const y Int)	
(declare-const z Int)
(declare-const i Int)	
(declare-const j Int)

; transfo 1
;; precondition

(declare-const pre-t1-trigger Bool)
(declare-const neg-pre-t1-trigger Bool)

(define-fun pre_t1 ((var10 Int)) Bool
            (= x var10))

(assert (or (not pre-t1-trigger)
            (pre_t1 0)
	)
)

(assert (or (not neg-pre-t1-trigger)
            (not (pre_t1 0))
	)
)

;; postcondition

(declare-const post-t1-trigger Bool)
(declare-const neg-post-t1-trigger Bool)

(define-fun post_t1 ((var11 Int)) Bool
            (= y var11))

(assert (or (not post-t1-trigger)
            (post_t1 0)
	)
)

(assert (or (not neg-post-t1-trigger)
            (not (post_t1 0))
	)
)

; transfo 2
;; preconditions

(declare-const pre-t2-trigger Bool)
(declare-const neg-pre-t2-trigger Bool)

(define-fun pre_t2 ((var20 Int)) Bool
             (= y var20))

(assert (or (not pre-t2-trigger)
            (pre_t2 0)
	)
)

(assert (or (not neg-pre-t2-trigger)
            (not (pre_t2 0))
	)
)

;; postcondition
(declare-const post-t2-trigger Bool)
(declare-const neg-post-t2-trigger Bool)

(define-fun post_t2 ((var21 Int)) Bool
            (= z var21))

(assert (or (not post-t2-trigger)
            (post_t2 0)
	)
)

(assert (or (not neg-post-t2-trigger)
            (not (post_t2 0))
	)
)

; transfo 3
;; precondition

(declare-const pre-t3-trigger Bool)
(declare-const neg-pre-t3-trigger Bool)

(define-fun pre_t3 ((var30 Int)) Bool
            (= x var30))

(assert (or (not pre-t3-trigger)
            (pre_t3 0)
	)
)

(assert (or (not neg-pre-t3-trigger)
            (not (pre_t3 0))
	)
)

;; postcondition

(declare-const post-t3-trigger Bool)
(declare-const neg-post-t3-trigger Bool)

(define-fun post_t3 ((var31 Int)) Bool
            (= z var31))

(assert (or (not post-t3-trigger)
            (post_t3 0)
	)
)

(assert (or (not neg-post-t3-trigger)
            (not (post_t3 0))
	)
)

; transfo 4
;; preconditions
(declare-const pre-t4-trigger Bool)
(declare-const neg-pre-t4-trigger Bool)

(define-fun pre_t4 ((var40 Int)) Bool
             (= z var40))

(assert (or (not pre-t4-trigger)
            (pre_t4 0)
	)
)

(assert (or (not neg-pre-t4-trigger)
            (not (pre_t4 0))
	)
)

;; postcondition

(declare-const post-t4-trigger Bool)
(declare-const neg-post-t4-trigger Bool)

(define-fun post_t4 ((var41 Int)) Bool
            (= y var41))

(assert (or (not post-t4-trigger)
            (post_t4 0)
	)
)

(assert (or (not neg-post-t4-trigger)
            (not (post_t4 0))
	)
)

; transfo 5
;; preconditions
(declare-const pre-t5-trigger Bool)
(declare-const neg-pre-t5-trigger Bool)

(define-fun pre_t5 ((var51 Int)) Bool
             (= i var51))

(assert (or (not pre-t5-trigger)
            (pre_t5 0)
	)
)

(assert (or (not neg-pre-t5-trigger)
            (not (pre_t5 0))
	)
)

;; postcondition

(declare-const post-t5-trigger Bool)
(declare-const neg-post-t5-trigger Bool)

(define-fun post_t5 ((var51 Int)) Bool
            (= j var51))

(assert (or (not post-t5-trigger)
            (post_t5 0)
	)
)

(assert (or (not neg-post-t5-trigger)
            (not (post_t5 0))
	)
)

; check satisfiability
(echo "checking completeness... (unsat = complete)")

(push)
(echo "for transfo 1...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger true))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled (excepted the one to test)
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 2...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger true))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled (excepted the one to test)
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 3...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger true))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled (excepted the one to test)
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 4...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger true))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled (excepted the one to test)
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger true))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 5...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger true))
;; postconditions must be enabled (excepted the one to test)
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger false))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(echo "checking determinism... (unsat = redundant input)")

(push)
(echo "for transfo 1...")
;; preconditions must be enabled excepted the one to test
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger true))
(assert (= pre-t3-trigger true))
(assert (= pre-t4-trigger true))
(assert (= pre-t5-trigger true))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger true))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions are unused
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger false))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 2...")
;; preconditions must be enabled excepted the one to test
(assert (= pre-t1-trigger true))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger true))
(assert (= pre-t4-trigger true))
(assert (= pre-t5-trigger true))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger true))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions are unused
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger false))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 3...")
;; preconditions must be enabled excepted the one to test
(assert (= pre-t1-trigger true))
(assert (= pre-t2-trigger true))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger true))
(assert (= pre-t5-trigger true))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger true))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions are unused
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger false))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 4...")
;; preconditions must be enabled excepted the one to test
(assert (= pre-t1-trigger true))
(assert (= pre-t2-trigger true))
(assert (= pre-t3-trigger true))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger true))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger true))
(assert (= neg-pre-t5-trigger false))
;; postconditions are unused
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger true))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 5...")
;; preconditions must be enabled excepted the one to test
(assert (= pre-t1-trigger true))
(assert (= pre-t2-trigger true))
(assert (= pre-t3-trigger true))
(assert (= pre-t4-trigger true))
(assert (= pre-t5-trigger false))
;; negation of preconditions must be tested
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger true))
;; postconditions are unused
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger false))
;; negation of postconditions are unused
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(echo "checking redundancy... (unsat = redundancy)")

(push)
(echo "for transfo 1...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions are unused
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled excepted the one to test
(assert (= post-t1-trigger false))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions must be tested
(assert (= neg-post-t1-trigger true))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 2...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions are unused
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled excepted the one to test
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger false))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions must be tested
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger true))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 3...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions are unused
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled excepted the one to test
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger false))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger true))
;; negation of postconditions must be tested
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger true))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 4...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions are unused
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled excepted the one to test
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger false))
(assert (= post-t5-trigger true))
;; negation of postconditions must be tested
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger true))
(assert (= neg-post-t5-trigger false))
(check-sat)
(pop)

(push)
(echo "for transfo 5...")
;; preconditions are unused
(assert (= pre-t1-trigger false))
(assert (= pre-t2-trigger false))
(assert (= pre-t3-trigger false))
(assert (= pre-t4-trigger false))
(assert (= pre-t5-trigger false))
;; negation of preconditions are unused
(assert (= neg-pre-t1-trigger false))
(assert (= neg-pre-t2-trigger false))
(assert (= neg-pre-t3-trigger false))
(assert (= neg-pre-t4-trigger false))
(assert (= neg-pre-t5-trigger false))
;; postconditions must be enabled excepted the one to test
(assert (= post-t1-trigger true))
(assert (= post-t2-trigger true))
(assert (= post-t3-trigger true))	
(assert (= post-t4-trigger true))
(assert (= post-t5-trigger false))
;; negation of postconditions must be tested
(assert (= neg-post-t1-trigger false))
(assert (= neg-post-t2-trigger false))
(assert (= neg-post-t3-trigger false))	
(assert (= neg-post-t4-trigger false))
(assert (= neg-post-t5-trigger true))
(check-sat)
(pop)
