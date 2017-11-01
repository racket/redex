#lang racket/base
(require redex "types.rkt")

;; ENDDEFS

;; EXAMPLE 1
(term (TC () ((λ X num X) 1)))
;; STOP 1

;; following:
;; type mismatch in application 
;; no types for free variable 
;; type checks

;; EXAMPLE tc
(test-equal 
 (term (TC () ((λ x (-> num num) x) 5)))
 (term #f))
;; CONTINUE tc
(test-equal 
 (term (TC () (+ x y)))
 (term #f))
;; CONTINUE tc
(test-equal
 (term (TC () (+ 1 2)))
 (term num))
;; CONTINUE tc
(test-equal
 (term (TC () (((λ x num (λ y num x)) 4) 2)))
 (term num))
;; CONTINUE tc
(test-results)
;; STOP tc 

;; EXAMPLE tc2
(test-equal
 (term (TC () ((λ x num 2) 4)))
 (term num))
;; CONTINUE tc2
(test-equal
 (term (TC () (((λ x num (λ y num x)) 2) 3)))
 (term num))
;; CONTINUE tc2
(test-equal
 (term (TC () (+ ((λ x num x) 1) 2)))
 (term num))
;; CONTINUE tc2
(test-results)
;; STOP tc2

;; EXAMPLE ex
(test-->> t-iswim-red
          (term ((λ x num 2) 4)) 2)
;; CONTINUE ex
(test-->> t-iswim-red
          (term (((λ x num (λ y num x)) 2) 3)) 2)
;; CONTINUE ex
(test-->> t-iswim-red 
          (term (+ ((λ x num x) 1) 2)) 3)
;; CONTINUE ex
(test-results)
;; STOP ex

(module+ main
;; START traces-bad
(traces t-iswim-red
        (term (((λ x num (λ y num x)) 2) 3))
        #:pred
        (λ (x) (term (TC () ,x))))
;; STOP traces-bad 

;; START traces-pred
(traces t-iswim-red
        (term (+ ((λ x num x) 1) 2))
        #:pred
        (λ (x) (term (TC () ,x))))
;; STOP traces-pred
)
