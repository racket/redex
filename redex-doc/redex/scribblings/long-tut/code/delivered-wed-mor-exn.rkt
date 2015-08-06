#lang racket

(require redex "common.rkt")

;; a calculus for 
(define-extended-language Exceptions Lambda
  (e ::= .... n +
     (raise e))
  (n ::= integer))

(define exceptions? (redex-match? Exceptions e))

(define c1
  (term
   ((lambda (x)
      (+ 1 (raise (+ 1 x))))
    0)))

(define c2
  (term
   (lambda (y)
     ((lambda (x)
        (+ 1 (raise (+ (raise -1) x))))
      0))))

(module+ test
  (test-equal (exceptions? c1) #true)
  (test-equal (exceptions? c2) #true))

(define-extended-language Exceptions-s Exceptions
  (C ::= hole (e ... C e ...) (lambda (x ...) C)
     (raise C))
  (E ::= hole (v ... E e ...)
     (raise E))
  (v ::= n + (lambda (x ...) e)))

(module+ test
  (test-->> ->βc c1 (term (raise 1)))
  #;
  (traces ->βc c1)
  (test-->> ->βc c2 (term (lambda (y) (raise -1)))))

(define ->βc
  (reduction-relation
   Exceptions-s
   (--> (in-hole C (in-hole E (raise v)))
        (in-hole C (raise v))
        (where #false ,(equal? (term E) (term hole)))
        ζ)
   (--> (in-hole C (+ n_1 n_2))
        (in-hole C ,(+ (term n_1) (term n_2)))
        +)
   (--> (in-hole C ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole C (subst ([e_1 x_1] ...) e))
        β)))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))