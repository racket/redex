#lang racket/base
(require redex/reduction-semantics)

;; START lang-syntax
(define-language bool-any-lang
  [B true 
     false
     (∨ B B)]
  [C (∨ C B)
     (∨ B C)
     hole])
;; STOP lang-syntax

;; START lang-C
(define C1 (term hole))
(define C2 (term (∨ (∨ false false) hole)))
(define C3 (term (∨ hole true)))
;; STOP lang-C

;; START lang-red
(define bool-any-red
  (reduction-relation
   bool-any-lang
   (--> (in-hole C (∨ true B))
        (in-hole C true)
        ∨-true)
   (--> (in-hole C (∨ false B))
        (in-hole C B)
        ∨-false)))
;; STOP lang-red

;; START B
(define B1 (term true))
(define B2 (term false))
(define B3 (term (∨ true false)))
(define B4 (term (∨ ,B1 ,B2)))
(define B5 (term (∨ false ,B4)))
;; STOP B

;; ENDDEFS

(provide C1 C2 C3
         B1 B2 B3 B4 B5
         bool-any-red bool-any-lang)
