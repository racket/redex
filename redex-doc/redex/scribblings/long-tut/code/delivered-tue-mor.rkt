#lang racket
(require redex "common.rkt" (only-in "mon-aft.rkt" fv))
(provide eval-value)

;; -- reductions for LC_v
;; -- standard reductions for LC_v
;; -- semantics for LC_v
;; -- cross-testing Racket with LC_v

(define-extended-language Lambda-calculus Lambda
  (e ::= .... n)
  (v ::= n (lambda (x ...) e))
  (n ::= number)
  (C ::= hole (e ... C e ...) (lambda (x_!_ ...) C)))

(define lambda? (redex-match? Lambda-calculus e))
(define context? (redex-match? Lambda-calculus C))

;; a metafunction that acts like a macro in Lambda-calculus
;; exercise 3 from Monday afternoon 
(define-metafunction Lambda-calculus
  ;;  let : ((x e) ...) e -> e but e plus hole 
  let : ((x any) ...) any -> any
  [(let ([x_lhs any_rhs] ...) any_body)
   ((lambda (x_lhs ...) any_body) any_rhs ...)])

(module+ test
  (define C1 (term ((lambda (x y) x) hole 1)))
  (define C2 (term ((lambda (x y) hole) 0 1)))
  (define C3 (term (let ([x hole][y 3]) (lambda (a) (a (x 1 y 2))))))
  
  (test-equal (context? C1) #true)
  (test-equal (context? C2) #true)
  (test-equal (context? C3) #true)
  
  (define e1 (term (in-hole ,C1 1)))
  (define e2 (term (in-hole ,C2 x)))
  (define e3 (term (in-hole ,C3 (lambda (x y z) x))))
  
  (test-equal (lambda? e1) #true)
  (test-equal (lambda? e2) #true)
  (test-equal (lambda? e3) #true))

;; model the λβv calculus, reductions only 

(module+ test
  ;; transitive closure testing 
  (test-->> -->βv #:equiv =α/racket e1 1)
  (test-->> -->βv #:equiv =α/racket e3 (term (lambda (a) (a 1))))
  
  ;; one-step reduction testing
  ;; reduces to TWO expressions 
  (define e4 ;; a term that contains TWO βv redexes 
    (term
     ((lambda (x y)
        [(lambda (f) (f (x 1 y 2)))
         (lambda (w) 42)])
      [(lambda (x) x) (lambda (a b c) a)]
      3)))

  (define e4-one-step
    (term
     ((lambda (x y)
        ((lambda (f) (f (x 1 y 2)))
         (lambda (w) 42)))
      (lambda (a b c) a)
      3)))
  (define e4-other-step
    (term
     ((lambda (x y)
        ((lambda (w) 42) (x 1 y 2)))
      ((lambda (x) x) (lambda (a b c) a))
      3)))
  
  (test--> -->βv #:equiv =α/racket e4 e4-other-step e4-one-step)
  (test-->> -->βv #:equiv =α/racket e4 42))

(define -->βv 
  (reduction-relation
   Lambda-calculus
   (--> (in-hole C ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole C (subst ([v_1 x_1] ...) e))
        βv)))

#;
(module+ test
  (traces -->βv e4))

;; model standard reduction for by-name and by-value calculus

(define-extended-language Standard Lambda-calculus
  (E ::= hole (v ... E e ...)))

(module+ test
  ;; yields only one term, leftmost-outermost
  (test--> s-->βv e4 e4-one-step))

(define s-->βv
  (reduction-relation
   Standard
   (--> (in-hole E ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole E (subst ((v_1 x_1) ...) e)))))

#;
(module+ test
  (traces s-->βv e4))

;; -----------------------------------------------------------------------------
;; a semantics

(module+ test
  (test-equal (term (eval-value ,e4)) 42)
  (test-equal (term (eval-value ,e4-one-step)) 42)
  (test-equal (term (eval-value ,e3)) 'closure))

(define-metafunction Standard
  eval-value : e -> v or closure or stuck 
  [(eval-value e) any_1 (where any_1 (run-value e))])

(define-metafunction Standard 
  run-value : e -> v or closure or stuck
  [(run-value n) n]
  [(run-value v) closure]
  [(run-value e)
   (run-value e_again)
   (where (e_again) ,(apply-reduction-relation s-->βv (term e)))]
  [(run-value any) stuck])

;; ---------------------------------------------------------

;; testing against Racket 

;; --- this is all Racket ---
(define-namespace-anchor A)
(define N (namespace-anchor->namespace A))
;; Lambda.e -> 
(define (racket-evaluator t0)
  (define result
    (with-handlers ((exn:fail? values))
      (eval t0 N)))
  (cond
    [(number? result) result]
    [(procedure? result) (term closure)]
    [else 'stuck]))
;; --- end of Racket magic 

(module+ test
  (test-equal (term (theorem:racket=eval-value ,e1)) #true)
  (test-equal (term (theorem:racket=eval-value ,e2)) #true)
  (test-equal (term (theorem:racket=eval-value ,e3)) #true)
  (test-equal (term (theorem:racket=eval-value ,e4)) #true))

(define-metafunction Standard
  theorem:racket=eval-value : e -> boolean
  [(theorem:racket=eval-value e)
   ,(equal? (racket-evaluator (term e)) (term (run-value e)))])


(module+ test
  (require "close.rkt")
  
  (redex-check Standard e
               (begin (displayln (term e))
                      (term (theorem:racket=eval-value e)))
               
               #:prepare (close-over-fv-with lambda?)

               #:attempts 12))







(module+ test
  (test-results))