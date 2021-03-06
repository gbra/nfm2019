(set-info :smt-lib-version 2.6)
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-option :produce-proofs true)

; input metamodel
;; sorts and constants
(declare-sort AADLProc 0)
(declare-sort AADLThread 0)
(declare-sort AADLDispatchProtocol 0)
(declare-const periodic AADLDispatchProtocol)
(declare-const sporadic AADLDispatchProtocol)
(declare-const aperiodic AADLDispatchProtocol)

;; predicates and functions on input sorts
(declare-fun linked (AADLThread AADLProc) Bool)
(declare-fun dispatch_protocol (AADLThread) AADLDispatchProtocol)
(declare-fun period (AADLThread) Int)

;; constraints on input sorts
(assert (forall ((t AADLThread))
        (exists ((p AADLProc)) (linked t p))))
;; not mandatory
;; si on active cette assertion il devrait y avoir un unsat sur le déterminisme de Map_Thread

; output metamodel
;; output sorts
(declare-sort CheddarCPU 0)
(declare-sort CheddarTask 0)

;; predicates on output sorts
(declare-fun linked (CheddarTask CheddarCPU) Bool)

;; constraints on output sorts
;; (assert (forall ((t CheddarTask))
;;        (exists ((p CheddarCPU)) (linked t p))))
;; not mandatory!

; AADL processor transformation rule
;; mapping function for transformation
(declare-fun apply_Map_Processor (AADLProc) Bool)

;; mapping function for transformation
(declare-fun Rp (AADLProc CheddarCPU) Bool)

;; preconditions
(declare-const pre-Map_Processor-input-trigger Bool)
(declare-const pre-Map_Processor-output-trigger Bool)
(declare-const pre-Map_Processor-trigger Bool)

(define-fun pre_Map_Processor_input ((proc AADLProc)) Bool
            true)

(assert (or (not pre-Map_Processor-input-trigger)
            (forall ((proc AADLProc)) (pre_Map_Processor_input proc))))

(define-fun pre_Map_Processor_output ((thread AADLProc)) Bool
            true)

(assert (or (not pre-Map_Processor-output-trigger)
            (forall ((proc AADLProc)) (pre_Map_Processor_output proc))))

(define-fun pre_Map_Processor ((proc AADLProc)) Bool
            (and (pre_Map_Processor_input proc) (pre_Map_Processor_output proc)))

(assert (or (not pre-Map_Processor-trigger)
            (forall ((proc AADLProc)) (pre_Map_Processor proc))))

;; postconditions
(declare-const post-Map_Processor-output-trigger Bool)
(declare-const post-Map_Processor_duplicated-output-trigger Bool)

(define-fun post_Map_Processor ((proc AADLProc)) Bool
            (exists ((cpu CheddarCPU)) (Rp proc cpu)))

(assert (or (not post-Map_Processor-output-trigger)
            (forall ((proc AADLProc)) (post_Map_Processor proc))))

(assert (or (not post-Map_Processor_duplicated-output-trigger)
            (forall ((proc AADLProc)) (post_Map_Processor proc))))

;; complete rule
(declare-const contract-Map_Processor-trigger Bool)
(assert (or (not contract-Map_Processor-trigger)
            (forall ((proc AADLProc))
                    (implies (implies (pre_Map_Processor proc) (apply_Map_Processor proc))
                             (post_Map_Processor proc)))))

; AADL thread transformation rule
;; mapping function for transformation
(declare-fun apply_Map_Thread (AADLThread) Bool)

;; mapping function for transformation
(declare-fun Rt (AADLThread CheddarTask) Bool)

;; preconditions
(declare-const pre-Map_Thread-input-trigger Bool)
(declare-const pre-Map_Thread-output-trigger Bool)
(declare-const pre-Map_Thread-trigger Bool)

(define-fun pre_Map_Thread_input ((thread AADLThread)) Bool
            (implies (or (= (dispatch_protocol thread) periodic)
                         (= (dispatch_protocol thread) sporadic))
                     (not (= (period thread) 0))))

(assert (or (not pre-Map_Thread-input-trigger)
            (forall ((thread AADLThread)) (pre_Map_Thread_input thread))))

(define-fun pre_Map_Thread_output
             ((thread AADLThread) (proc AADLProc) (cpu CheddarCPU)) Bool
             (and (linked thread proc) (Rp proc cpu)))

;; la seconde partie n'a pas d'intérêt pour la négation

(assert (or (not pre-Map_Thread-output-trigger)
            (forall ((thread AADLThread))
                    (exists ((proc AADLProc) (cpu CheddarCPU))
                       (pre_Map_Thread_output thread proc cpu)))))

(define-fun pre_Map_Thread
    ((thread AADLThread) (proc AADLProc) (cpu CheddarCPU)) Bool
    (and (pre_Map_Thread_input thread) (pre_Map_Thread_output thread proc cpu)))

(assert (or (not pre-Map_Thread-trigger)
            (forall ((thread AADLThread))
                    (exists ((proc AADLProc) (cpu CheddarCPU))
                       (pre_Map_Thread thread proc cpu)))))

;; postconditions
(declare-const post-Map_Thread-output-trigger Bool)

(define-fun post_Map_Thread
    ((thread AADLThread) (cpu CheddarCPU)) Bool
    (exists ((task CheddarTask))
       (and
        (Rt thread task)
        (linked task cpu)
        (forall ((thread2 AADLThread))
                 (implies (not (= thread thread2))
                          (not (Rt thread2 task))))
        )))

(assert (or (not post-Map_Thread-output-trigger)
            (forall ((thread AADLThread)) (exists ((cpu CheddarCPU))
                                             (post_Map_Thread thread cpu)))))

;; complete rule
(declare-const contract-Map_Thread-trigger Bool)
(assert (or (not contract-Map_Thread-trigger)
            (forall ((thread AADLThread) (proc AADLProc) (cpu CheddarCPU))
                    (implies (implies (pre_Map_Thread thread proc cpu) (apply_Map_Thread thread))
                             (post_Map_Thread thread cpu)))))

; negation of conditions (for reasoning only)
;; Map_Processor

(declare-const neg-pre-Map_Processor-input-trigger Bool)
(declare-const neg-pre-Map_Processor-output-trigger Bool)
(declare-const neg-post-Map_Processor-output-trigger Bool)

(assert (or (not neg-pre-Map_Processor-input-trigger)
            (exists ((proc AADLProc)) (not (pre_Map_Processor_input proc)))))

(assert (or (not neg-pre-Map_Processor-output-trigger)
            (exists ((proc AADLProc)) (not (pre_Map_Processor_output proc)))))

(assert (or (not neg-post-Map_Processor-output-trigger)
            (exists ((proc AADLProc)) (not (post_Map_Processor proc)))))

;; Map_Thread

(declare-const neg-pre-Map_Thread-input-trigger Bool)
(declare-const neg-pre-Map_Thread-output-trigger Bool)
(declare-const neg-post-Map_Thread-output-trigger Bool)

(assert (or (not neg-pre-Map_Thread-input-trigger)
            (exists ((thread AADLThread)) (not (pre_Map_Thread_input thread)))))

(assert (or (not neg-pre-Map_Thread-output-trigger)
            (exists ((thread AADLThread))
                    (forall ((proc AADLProc) (cpu CheddarCPU))
                       (not (pre_Map_Thread_output thread proc cpu))))))

(assert (or (not neg-post-Map_Thread-output-trigger)
            (exists ((thread AADLThread)) (forall ((cpu CheddarCPU))
                                             (not (post_Map_Thread thread cpu))))))

; check satisfiability

;; unused triggers are deactivated
(assert (= pre-Map_Processor-trigger false))
(assert (= contract-Map_Processor-trigger false))
(assert (= pre-Map_Thread-trigger false))
(assert (= contract-Map_Thread-trigger false))

;; completeness
(echo "checking completeness... (unsat = ok)")

(echo "for Map_Processor...")

(push)
;; preconditions are unused
(assert (= pre-Map_Processor-input-trigger false))
(assert (= pre-Map_Processor-output-trigger false))
(assert (= pre-Map_Thread-input-trigger false))
(assert (= pre-Map_Thread-output-trigger false))

;; negation of preconditions must be tested
(assert (= neg-pre-Map_Processor-input-trigger true))
(assert (= neg-pre-Map_Processor-output-trigger true))
(assert (= neg-pre-Map_Thread-input-trigger false))
(assert (= neg-pre-Map_Thread-output-trigger false))

;; postconditions must be enabled (excepted the one to test)
(assert (= post-Map_Processor-output-trigger false))
(assert (= post-Map_Thread-output-trigger true))

;; negation of postconditions are unused
(assert (= neg-post-Map_Processor-output-trigger false))
(assert (= neg-post-Map_Thread-output-trigger false))
(check-sat)
(pop)

(echo "for Map_Thread...")

(push)
;; preconditions are unused
(assert (= pre-Map_Processor-input-trigger false))
(assert (= pre-Map_Processor-output-trigger false))
(assert (= pre-Map_Thread-input-trigger false))
(assert (= pre-Map_Thread-output-trigger false))

;; negation of preconditions must be tested
(assert (= neg-pre-Map_Processor-input-trigger false))
(assert (= neg-pre-Map_Processor-output-trigger false))
(assert (= neg-pre-Map_Thread-input-trigger false))
(assert (= neg-pre-Map_Thread-output-trigger true))

;; postconditions must be enabled (excepted the one to test)
;; !test: desactivating the Map-Processor postcondition must cause Map_Thread to be incomplete (= result must be sat) 
(assert (= post-Map_Processor-output-trigger true))
(assert (= post-Map_Thread-output-trigger false))

;; negation of postconditions are unused
(assert (= neg-post-Map_Processor-output-trigger false))
(assert (= neg-post-Map_Thread-output-trigger false))
(check-sat)
(pop)

;; determinism
(echo "checking determinism... (unsat = nok)")

(echo "for Map_Processor...")

(push)
;; preconditions must be enabled excepted the one to test
(assert (= pre-Map_Processor-input-trigger false))
(assert (= pre-Map_Processor-output-trigger false))
(assert (= pre-Map_Thread-input-trigger true))
(assert (= pre-Map_Thread-output-trigger true))

;; negation of preconditions must be tested
(assert (= neg-pre-Map_Processor-input-trigger false))	; this neg-pre should normally be set to true but the result will always be unsat (because the precondition is always true)
(assert (= neg-pre-Map_Processor-output-trigger false)) ; this neg-pre should normally be set to true but the result will always be unsat (because the precondition is always true)
(assert (= neg-pre-Map_Thread-input-trigger false))
(assert (= neg-pre-Map_Thread-output-trigger false))

;; postconditions are unused
(assert (= post-Map_Processor-output-trigger false))
(assert (= post-Map_Thread-output-trigger false))

;; negation of postconditions are unused
(assert (= neg-post-Map_Processor-output-trigger false))
(assert (= neg-post-Map_Thread-output-trigger false))
(check-sat)
;; (get-proof)
(pop)

(echo "for Map_Thread...")

(push)
;; preconditions must be enabled excepted the one to test
(assert (= pre-Map_Processor-input-trigger true))
(assert (= pre-Map_Processor-output-trigger true))
;; !test: activating one of the Map-Thread preconditions must cause Map_Thread to be not deterministic (= result must be unsat) 
(assert (= pre-Map_Thread-input-trigger false))
(assert (= pre-Map_Thread-output-trigger false))

;; negation of preconditions must be tested
(assert (= neg-pre-Map_Processor-input-trigger false))
(assert (= neg-pre-Map_Processor-output-trigger false))
(assert (= neg-pre-Map_Thread-input-trigger true))
(assert (= neg-pre-Map_Thread-output-trigger true))

;; postconditions are unused
(assert (= post-Map_Processor-output-trigger false))
(assert (= post-Map_Thread-output-trigger false))

;; negation of postconditions are unused
(assert (= neg-post-Map_Processor-output-trigger false))
(assert (= neg-post-Map_Thread-output-trigger false))

(check-sat)
;(check-sat-assuming (neg-pre-Map_Thread-input-trigger neg-pre-Map_Thread-output-trigger pre-Map_Processor-input-trigger pre-Map_Processor-output-trigger))
; (check-sat-assuming (neg-pre-Map_Thread-output-trigger))
; (get-unsat-assumptions)
; (get-unsat-core)
;; (get-proof)
(pop)

(echo "checking redundancy... (unsat = nok)")

(echo "for Map_Processor...")

(push)
;; preconditions are unused
(assert (= pre-Map_Processor-input-trigger false))
(assert (= pre-Map_Processor-output-trigger false))
(assert (= pre-Map_Thread-input-trigger false))
(assert (= pre-Map_Thread-output-trigger false))

;; negation of preconditions are unused
(assert (= neg-pre-Map_Processor-input-trigger false))
(assert (= neg-pre-Map_Processor-output-trigger false))
(assert (= neg-pre-Map_Thread-input-trigger false))
(assert (= neg-pre-Map_Thread-output-trigger false))

;; postconditions must be enabled excepted the one to test
;; !test: activating the Map-Processor(_duplicated) postcondition must cause Map_Processor to be redundant (= result must be unsat) 
(assert (= post-Map_Processor-output-trigger false))
(assert (= post-Map_Processor_duplicated-output-trigger false))
(assert (= post-Map_Thread-output-trigger true))

;; negation of postconditions must be tested
(assert (= neg-post-Map_Processor-output-trigger true))
(assert (= neg-post-Map_Thread-output-trigger false))

;; check satisfiability
(check-sat)
; (check-sat-assuming (post-Map_Thread-output-trigger neg-post-Map_Processor-output-trigger))
;; (check-sat-assuming (neg-post-Map_Processor-output-trigger))
;; (get-unsat-assumptions)
;; (get-unsat-core)
;; (get-proof)
(pop)

(echo "for Map_Thread...")

(push)
;; preconditions are unused
(assert (= pre-Map_Processor-input-trigger false))
(assert (= pre-Map_Processor-output-trigger false))
(assert (= pre-Map_Thread-input-trigger false))
(assert (= pre-Map_Thread-output-trigger false))

;; negation of preconditions are unused
(assert (= neg-pre-Map_Processor-input-trigger false))
(assert (= neg-pre-Map_Processor-output-trigger false))
(assert (= neg-pre-Map_Thread-input-trigger false))
(assert (= neg-pre-Map_Thread-output-trigger false))

;; postconditions must be enabled excepted the one to test
(assert (= post-Map_Processor-output-trigger true))
(assert (= post-Map_Thread-output-trigger false))

;; negation of postconditions must be tested
(assert (= neg-post-Map_Processor-output-trigger false))
(assert (= neg-post-Map_Thread-output-trigger true))
(check-sat)
(pop)

(exit)
