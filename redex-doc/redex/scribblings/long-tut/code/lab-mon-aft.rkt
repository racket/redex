#lang racket

(require redex "common.rkt")

;; -----------------------------------------------------------------------------
;; (bv e) computes the sequence of bound variables in e
;; A variable is bound if it occurs in a lambda-parameter sequence

(module+ test
  (test-equal (term (bv (lambda (x y) (lambda (z) (x y z))))) (term (x y z))))

(define-metafunction Lambda
  bv : e -> (x ...)
  [(bv x) ()]
  [(bv (lambda (x ...) e))
   (x ... x_e ...)
   (where (x_e ...) (bv e))]
  [(bv (e_f e_a ...))
   (x_f ... x_a ... ...)
   (where (x_f ...) (bv e_f))
   (where ((x_a ...) ...) ((bv e_a) ...))])


;; -----------------------------------------------------------------------------
;; (lookup x env) determines x's leftmost value in env

(define-extended-language Env Lambda
  (e ::= .... natural)
  (env ::= ((x e) ...)))

(define env1 (term ()))
(define env2 (term ((y 1) (z 2) (x 0) (x 9) (w 3))))

(define Env? (redex-match? Env env))

(module+ test
  (test-equal (Env? env1) #true)
  (test-equal (Env? env2) #true))

(module+ test
  (test-equal (term (lookup x ,env1)) #false)
  (test-equal (term (lookup x ,env2)) 0))

(define-metafunction Env
  lookup : x env -> e or #false
  [(lookup x ((x_1 e_1) ... (x e) (x_2 e_2) ...))
   e
   (where #false (in x (x_1 ...)))]
  [(lookup x env) #false])

;; -----------------------------------------------------------------------------
;; let: see tue-mor

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
