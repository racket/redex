#lang racket

(provide
 ;; language 
 TLambda-tc

 ;; (extend Γ (x t) ...) add (x t) to Γ so that x is found before other x-s
 extend

 ;; (lookup Γ x) retrieves x's type from Γ
 lookup)

(require redex)

;; -----------------------------------------------------------------------------
(define-language TLambda-tc
  (e ::= n + x (lambda ((x_!_ t) ...) e) (e e ...))
  (n ::= natural)
  (t ::= int (t ... -> t))
  (Γ ::= ((x t) ...))
  (x ::= variable-not-otherwise-mentioned))

(define tlambda? (redex-match? TLambda-tc e))

;; -----------------------------------------------------------------------------
;; (extend Γ (x t) ...) add (x t) to Γ so that x is found before other x-s

(module+ test
  (test-equal (term (extend () (x int))) (term ((x int)))))

(define-metafunction TLambda-tc
  extend : Γ (x any) ... -> any
  [(extend ((x_Γ any_Γ) ...) (x any) ...) ((x any) ...(x_Γ any_Γ) ...)])

;; -----------------------------------------------------------------------------
;; (lookup Γ x) retrieves x's type from Γ

(module+ test
  (test-equal (term (lookup ((x int) (x (int -> int)) (y int)) x)) (term int))
  (test-equal (term (lookup ((x int) (x (int -> int)) (y int)) y)) (term int)))
  
(define-metafunction TLambda-tc
  lookup : any x -> any or #f
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   #f])
