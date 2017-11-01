#lang scheme
(require redex "ck.rkt" "../iswim/iswim.rkt")

;; ENDDEFS

;; EXAMPLE arr
(apply-reduction-relation* iswim-red
                           (term ((λ x (- x 1)) 2)))
;; STOP arr


;; EXAMPLE sub-test
(test-predicate same-ck-stdred? (term ((λ x (- x 1)) 2)))
;; STOP sub-test

