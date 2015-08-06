#lang racket

;; a type reduction-based approach to type checking

(require redex "common.rkt")

;; -----------------------------------------------------------------------------
;; syntax 
(define-language TLambda
  (e ::= n x (lambda (x t) e) (e e) (+ e e))
  (n ::= number)
  (t ::= int (t -> t))
  (x ::= variable-not-otherwise-mentioned))

(define in-TLambda? (redex-match? TLambda e))

;; -----------------------------------------------------------------------------
;; examples

(define e1
  (term (lambda (x int) (lambda (f (int -> int)) (+ (f (f x)) (f x))))))
  
(define e2
  (term
   (lambda (x int)
     (lambda (f ((int -> int) -> int))
       (f x)))))
(define e3 (term (lambda ((x int)) (int -> int))))

(module+ test
  (test-equal (in-TLambda? e1) #true)
  (test-equal (in-TLambda? e2) #true)
  (test-equal (in-TLambda? e3) #false))

;; -----------------------------------------------------------------------------
;; (⊢ Γ e t) -- the usual type judgment for an LC language

(define-extended-language TLambda-tc TLambda
  (e ::= .... t (t -> e))
  (C ::= hole (lambda (x t) C) (C e) (e C) (+ C e) (+ e C) (t -> C)))

(module+ test
  (test-equal (term (tc ,e1)) (term (int -> ((int -> int) -> int))))
  
  ;; a failure -- no types are returned 
  (test-equal (term (tc ,e2)) #false))

(define-metafunction TLambda-tc
  tc : e -> t or #false
  [(tc t) t]
  [(tc e)
   (tc e_again)
   (where (e_again e_more ...) ,(apply-reduction-relation ->tc (term e)))]
  [(tc e_stuck) #false])

(define ->tc
  (reduction-relation
   TLambda-tc
   (--> (in-hole C n) (in-hole C int))
   (--> (in-hole C (+ int int)) (in-hole C int))
   (--> (in-hole C (lambda (x t) e)) (in-hole C (t -> (subst ((t x)) e))))
   (--> (in-hole C ((t -> t_range) t)) (in-hole C t_range))))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
