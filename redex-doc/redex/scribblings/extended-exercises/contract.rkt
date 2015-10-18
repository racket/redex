#lang racket

;; a model of contracts in a call-by-value functional language

(require redex "common.rkt")

;; -----------------------------------------------------------------------------
;; syntax 
(define-language Lambda
  (e ::=
     x (lambda (x) e) (e e)
     n (+ e e)
     (if0 e e e)
     (c · e x x) ;; monitor a contract
     (blame x))
  (n ::= number)
  (c ::= num? even? odd? pos? (c -> c))
  (x ::= variable-not-otherwise-mentioned))

;; -----------------------------------------------------------------------------
;; examples

(define a-module (term {(even? -> pos?) · (lambda (x) (+ x 1)) server client}))
(define p-good (term [,a-module 2]))
(define p-bad-server (term [,a-module -2]))
(define p-bad-client (term [,a-module 1]))

(module+ test
  (test-equal (redex-match? Lambda c (term (even? -> pos?))) #t)
  (test-equal (redex-match? Lambda e p-good) #true)
  (test-equal (redex-match? Lambda e
                            (term
                             {(even? -> pos?) · (lambda (x) (+ x 1))
                                              server
                                              client})) #true)
  
  (test-equal (redex-match? Lambda e p-bad-server) #true)
  (test-equal (redex-match? Lambda e p-bad-client) #true))

;; -----------------------------------------------------------------------------
;; the standard reductions 

(define-extended-language Lambda-calculus Lambda
  (v ::= n (lambda (x) e))
  (E ::= hole
     (v ... E e ...)
     (+ v ... E e ...)
     (c · E x x)))

(module+ test
  (test-->> s-->c #:equiv =α/racket p-good 3)
  (test-->> s-->c #:equiv =α/racket p-bad-client (term (blame client)))
  (test-->> s-->c #:equiv =α/racket p-bad-server (term (blame server))))

(define s-->c 
  (reduction-relation
   Lambda-calculus
   (--> (in-hole E ((lambda (x) e) v)) (in-hole E (subst ([v x]) e)) βv)
   (--> (in-hole E (+ n_1 n_2)) (in-hole E ,(+ (term n_1) (term n_2))) +)
   (--> (in-hole E (if0 0 e_then e_else)) (in-hole E e_then) if0-true)
   (--> (in-hole E (if0 v e_then e_else))
        (in-hole E e_then)
        (where #false (zero? (term v)))
        if0-false)
   (--> (in-hole E (pos? · n x_s x_c))
        (in-hole E ,(c positive? (term n) (term x_s) (term x_c)))
        pos)
   (--> (in-hole E (even? · n x_s x_c))
        (in-hole E ,(c even? (term n) (term x_s) (term x_c)))
        even)
   (--> (in-hole E (odd? · n x_s x_c))
        (in-hole E ,(c odd? (term n) (term x_s) (term x_c)))
        odd)
   (--> (in-hole E (num? · n x_s x_c))
        (in-hole E 0)
        num)
   (--> (in-hole E ((c_1 -> c_2) · (lambda (x) e) x_s x_c))
        (in-hole E
                 (lambda (x)
                   (c_2 · ((lambda (x) e) (c_1 · x x_c x_s)) x_s x_c))))
   (--> (in-hole E (blame x))
        (blame x)
        (where #false ,(equal? (term hole) (term E)))
        blame)))

(define (c pred? n server client)
  (if (pred? n) n (term (blame ,server))))

#;
(module+ test
  (traces -->βv p-bad-client))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))

