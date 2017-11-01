#lang scheme
(require redex "ck.ss" "../iswim/iswim.ss")

;; ENDDEFS

;; EXAMPLE arr
(apply-reduction-relation* iswim-red
                           (term ((λ x (- x 1)) 2)))
;; STOP arr


;; EXAMPLE sub-test
(test-predicate same-ck-stdred? (term ((λ x (- x 1)) 2)))
;; STOP sub-test

