#lang racket

;; a SEMANTICS for a Lambda-language with variable assignment statements
;;   -- equipping a semantics with a store
;;   -- variables as locations 
;; a CALCULUS for a Lambda-language with a raise-exception expression 
;;   -- erasing evaluation contexts 

;; -----------------------------------------------------------------------------
(require redex "common.rkt" "extend-lookup.rkt")

(define-extended-language Assignments Lambda
  (e ::= .... n +
     (void)
     (set! x e))
  (n ::= natural))

;; (let ((x_1 x_2) ...) e_1 e_2) binds the current value of x_2 to x_1,
;; evaluates e_1, throws away its value, and finally evaluates e_2 
(define-metafunction Assignments
  let : ((x e) ...) e e -> e
  [(let ([x_lhs e_rhs] ...) e_1 e_2)
   ((lambda (x_lhs ...)
      ((lambda (x_dummy) e_2) e_1))
    e_rhs ...)
   (where (x_dummy) ,(variables-not-in (term (e_1 e_2)) '(dummy)))])

(define assignments? (redex-match? Assignments e))

(define e1
  (term
   (lambda (x)
     (lambda (y)
       (let ([tmp x])
         (set! x (+ y 1))
         tmp)))))

(define p-1 (term ((,e1 1) 2)))

(define e2
  (term
   ((lambda (x)
      (let ([tmp x])
        (set! x y)
        tmp))
    (let ([tmp-z z])
      (set! z (+ z 1))
      (let ([tmp-y y])
        (set! y tmp-z)
        tmp-y)))))

(define p-2 (term ((lambda (y) ((lambda (z) ,e2) 1)) 2)))

(define p-c (term +))

(module+ test
  (test-equal (assignments? e2) #true)
  (test-equal (assignments? e1) #true)
  (test-equal (assignments? p-1) #true)
  (test-equal (assignments? p-2) #true)
  (test-equal (assignments? p-c) #true))

;; -------------------------------------------------------

;; -------------------------------------------------------------------
;; stores for a semantics 

(define-extended-language Assignments-s Assignments
  (E ::= hole (v ... E e ...)
     (set! x E))
  (σ ::= ((x v) ...))
  (v ::= n + (lambda (x ...) e)
     (void)))


;; -------------------------------------------------------
;; the standard reduction
(module+ test
  (define es
    (term
     ((lambda (x)
        ((lambda (y) x)
         (let ([tmp x]) (set! x 1) tmp)))
      0)))

  (test-->>∃ s->βs (term [,es ()]) (redex-match? Assignments-s [1 σ]))
  
  (define e-bug
    (term
     (let ([x 42])
       (void)
       (let ([x 84])
         (void)
         x))))
  
  (test-->>∃ s->βs (term [,e-bug ()])
             (redex-match? Assignments-s [84 σ]))
  #;
  (traces s->βs (term [,e-bug ()])))

(define s->βs
  (reduction-relation
   Assignments-s
   #:domain (e σ)
   (--> [(in-hole E x) σ]
        [(in-hole E (lookup σ x)) σ])
   (--> [(in-hole E (set! x v)) σ]
        [(in-hole E (void)) (extend σ (x) (v))])
   (--> [(in-hole E (+ n_1 n_2)) σ]
        [(in-hole E ,(+ (term n_1) (term n_2))) σ])
   (--> [(in-hole E ((lambda (x ..._n) e) v ..._n)) σ]
        [(in-hole E (subst ((x_new x) ...) e))
         (extend σ (x_new ...) (v ...))]
        (where (x_new ...) ,(variables-not-in (term σ) (term (x ...)))))))



(module+ test
  (test-results))

