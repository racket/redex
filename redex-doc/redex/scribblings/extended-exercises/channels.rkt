#lang racket

;; a model of channel-based communication in a by-value language with threads

(require redex "common.rkt")

(define-language Lambda
  (e ::=
     x (lambda (x_!_ ...) e) (e e ...)
     n (+ e e)
     (if0 e e e)
     (spawn e)
     (put c e)
     (void)
     (get c))
  (n ::= number)
  (c ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned))

;; auxiliary syntax 

;; a metafunction that acts like a macro in Lambda-calculus
;; exercise 3 from Monday afternoon 
(define-metafunction Lambda
  ;;  let : ((x e) ...) e -> e but e plus hole 
  let : ((x any) ...) any -> any
  [(let ([x_lhs any_rhs] ...) any_body)
   ((lambda (x_lhs ...) any_body) any_rhs ...)])

;; -----------------------------------------------------------------------------
;; examples 

(define e0 (term (put x 5)))
(define e1 (term (get x)))
(define e2 (term (let ([_a (spawn ,e0)] [_b (spawn ,e1)]) 1)))
(define p0 (term (let ([c y]) ,e2)))

(module+ test
  (test-equal (redex-match? Lambda e e0) #true)
  (test-equal (redex-match? Lambda e e1) #true)
  (test-equal (redex-match? Lambda e p0) #true))

;; -----------------------------------------------------------------------------
;; a standard reduction relation 

(define-extended-language Lambda-calculus Lambda
  (s ::= (e ...))
  (v ::= n c (void) (lambda (x ...) e))
  (E ::= hole
     (v ... E e ...)
     (+ v ... E e ...)))

(define s1 (term (,e0 ,e1 ,e1)))
(module+ test
  (test-equal (redex-match? Lambda-calculus s s1) #true)
  (test-->> s-->comm #:equiv =α/racket
            (term (,p0))
            (term (1 5 (void)))))

(define s-->comm 
  (reduction-relation
   Lambda-calculus
   (--> (e_1 ... (in-hole E ((lambda (x ..._n) e) v ..._n)) e_2 ...)
        (e_1 ... (in-hole E (subst ([v x] ...) e)) e_2 ...)
        βv)
   (--> (e_1 ... (in-hole E (spawn e)) e_2 ...)
        (e_1 ... (in-hole E (void)) e e_2 ...)
        spawn)
   (--> (e_1 ... (in-hole E (get x)) e_2 ... (in-hole E (put x v)) e_3 ...)
        (e_1 ... (in-hole E v) e_2 ... (in-hole E (void)) e_3 ...)
        message-left)
   (--> (e_1 ... (in-hole E (put x v)) e_2 ... (in-hole E (get x)) e_3 ...)
        (e_1 ... (in-hole E v) e_2 ... (in-hole E (void)) e_3 ...)
        message-right)
   (--> (e_1 ... (in-hole E (+ n_1 n_2)) e_2 ...)
        (e_1 ... (in-hole E ,(+ (term n_1) (term n_2))) e_2 ...)
        +)
   (--> (e_1 ... (in-hole E (if0 0 e_then e_else)) e_2 ...)
        (e_1 ... (in-hole E e_then) e_2 ...)
        if0-true)
   (--> (e_1 ... (in-hole E (if0 v e_then e_else)) e_2 ...)
        (e_1 ... (in-hole E e_then) e_2 ...)
        (where #false (zero? (term v)))
        if0-false)))

(module+ main
  (traces s-->comm s1))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))

