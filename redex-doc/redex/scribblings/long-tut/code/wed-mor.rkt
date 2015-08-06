#lang racket

(require redex "common.rkt" "extend-lookup.rkt")
(provide Assignments e2)

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

;; -------------------------------------------------------------------
;; stores for a semantics 

(define-extended-language Assignments-s Assignments
  (E ::= hole (v ... E e ...)
     (set! x E))
  (σ ::= ((x v) ...))
  (v ::= n + (lambda (x ...) e)
     (void)))

;; -----------------------------------------------------------------------------
;; a standrd reduction relation for Assignments

(module+ test
  (define es
    (term
     ((lambda (x)
        ((lambda (y) x)
         (let ([tmp x]) (set! x 1) tmp)))
      0)))

  (test-->>∃ s->βs (term [,es ()]) (redex-match? Assignments-s [1 σ])))

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
        [(in-hole E e) (extend σ (x_new ...) (v ...))]
        (where (x_new ...) ,(variables-not-in (term σ) (term (x ...)))))))

;; -----------------------------------------------------------------------------
;; a semantics for Assignments

(module+ test
  (test-equal (term (eval-assignments ,p-1)) 1)
  (test-equal (term (eval-assignments ,p-2)) 2)
  (test-equal (term (eval-assignments ,p-c)) (term closure)))

(define-metafunction Assignments-s
  eval-assignments : e -> v or closure
  [(eval-assignments e) (run-assignments (e ()))])

(define-metafunction Assignments-s
  run-assignments : (e σ) -> v or closure
  [(run-assignments (n σ)) n]
  [(run-assignments (v σ)) closure]
  [(run-assignments any_1)
   (run-assignments any_again)
   (where (any_again) ,(apply-reduction-relation s->βs (term any_1)))]
  [(run-assignments any) stuck])

;; =============================================================================
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

;; -----------------------------------------------------------------------------

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
   (--> (in-hole C ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole C (subst ([v_1 x_1] ...) e))
        β_v)))

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
