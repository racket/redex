#lang scheme/base

(require redex)

;; START lang
(define-language bool-standard-lang
  [B true 
     false
     (∨ B B)]
  [E (∨ E B)
     hole])

(define bool-standard-red
  (reduction-relation
   bool-standard-lang
   (--> (in-hole E (∨ true B))
        (in-hole E true)
        ∨-true)
   (--> (in-hole E (∨ false B))
        (in-hole E B)
        ∨-false)))
;; STOP lang 

;; START E
(define E1 (term hole))
(define E2 (term (∨ hole true)))
(define E3 (term (∨ (∨ hole false) false)))
;; STOP E

;; ENDDEFS

(provide E1 E2 E3 bool-standard-lang bool-standard-red)
