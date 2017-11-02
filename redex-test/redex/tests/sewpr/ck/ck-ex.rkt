#lang racket/base
(require redex/reduction-semantics "ck.rkt" "../iswim/iswim.rkt")

;; ENDDEFS

;; EXAMPLE arr
(apply-reduction-relation* iswim-red
                           (term ((λ x (- x 1)) 2)))
;; STOP arr


;; EXAMPLE sub-test
(test-predicate same-ck-stdred? (term ((λ x (- x 1)) 2)))
;; STOP sub-test


;; ensure drdr only compiles this,
;; as it intentionally errors
(module test racket/base)
