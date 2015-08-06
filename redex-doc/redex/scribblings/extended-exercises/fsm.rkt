#lang racket

;; modeling the transitions in non-deterministic finite-state machines 

(require redex)

;; -----------------------------------------------------------------------------
;; syntax 

(define-language L
  [FSM (rule ...)]
  [rule [state -> input -> state]]
  [state variable-not-otherwise-mentioned]
  [input variable-not-otherwise-mentioned])

;; -----------------------------------------------------------------------------
;; the reduction system

(module+ test
  (define fsm1 (term ([a -> x -> b]
                      [a -> y -> c]
                      [b -> x -> a])))
  
  (test-->> -->fsm
            (term [,fsm1
                   a
                   (x x y)])
            (term [,fsm1
                   c
                   ()]))
  (test-->> -->fsm
            (term [,fsm1
                   a
                   (x x y x)])
            (term [,fsm1
                   c
                   (x)]))
  
  (define fsm2 (term ([a -> x -> b]
                      [a -> y -> c]
                      [a -> y -> d]
                      [b -> x -> a]
                      [d -> x -> b])))
  (test-->>∃ -->fsm
             (term [,fsm2
                    a
                    (x x y x)])
             (term [,fsm2
                    b
                    ()])))

(define -->fsm
  (reduction-relation
   L
   #:domain [FSM state (input ...)]
   (--> [FSM state_1 (input_0 input_1 ...)]
        [FSM state_2 (input_1 ...)]
        (where (_ ... [state_1 -> input_0 -> state_2] _ ...)
               FSM))))

(module+ test
  (test-results))