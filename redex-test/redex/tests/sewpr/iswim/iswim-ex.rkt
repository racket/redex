#lang scheme

(require "iswim.rkt")
(require redex)

;; ENDDEFS

;; EXAMPLEN ellipses
(redex-match iswim (in-hole E number) (term (+ 1 2)))
;; STOP ellipses

;; EXAMPLE delta1
(term (δ (iszero 0)))
;; STOP delta1

;; EXAMPLE delta2
(term (δ (iszero 2)))
;; STOP delta2

;; EXAMPLE delta3
(term (δ (+ 1 2)))
;; STOP delta3

;; EXAMPLE subst-dup
(term (subst (λ p p) p 2))
;; STOP subst-dup

;; EXAMPLE subst-plus
(term (subst (+ x (- y z)) z 5))
;; STOP subst-plus

;; EXAMPLE subst-rename
(term (subst (λ f (f z)) z (λ y f)))
;; STOP subst-rename


(provide iswim-red)
