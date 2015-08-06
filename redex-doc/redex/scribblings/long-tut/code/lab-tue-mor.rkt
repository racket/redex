#lang racket

(require redex "common.rkt")

(define-extended-language Lambda-η Lambda
  (e ::= .... n)
  (n ::= natural)
  (C ::=
     hole
     (e ... C e ...)
     (lambda (x_!_ ...) C))
  (E ::=
     hole
     (E e ...))
  (v ::=
     n
     (lambda (x ...) e)))

(define lambda? (redex-match? Lambda-η e))

;; -----------------------------------------------------------------------------
;; exercise: develop beta-eta calculus 

(module+ test
  (define t2
    (term
     ((lambda (x) (x ((lambda (x) (1 x))))) 2)))
  (define t3
    (term
     ((lambda (x)
        ((lambda (y z)
           (x y z))
         1 2))
      (lambda (a b) a))))
  (test-equal (lambda? t2) #true)
  (test-equal (lambda? t3) #true)
  
  (test-->  -->βη
            #:equiv =α/racket
            t2
            (term ((lambda (x) (x (1))) 2))
            (term (2 ((lambda (x) (1 x))))))
  
  (test--> -->βη
           #:equiv =α/racket
           t3
           (term
            ((lambda (y z)
               ((lambda (a b) a) y z))
             1 2))
           (term
            ((lambda (x) (x 1 2))
             (lambda (a b) a))))
  
  (test-->> -->βη
            #:equiv =α/racket
            t2
            (term (2 (1))))
  (test-->> -->βη t3 1)
  
  #;
  (traces -->βη t2))

(define -->βη
  (reduction-relation
   Lambda-η
   #:domain e
   (--> (in-hole C (lambda (x ...) (e x ...)))
        (in-hole C e)
        η)
   (--> (in-hole C ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole C (subst ([e_1 x_1] ...) e))
        β)))

;; -----------------------------------------------------------------------------
;; beta and beta-eta standard reduction 
(module+ test
  
  (test-->  s-->βη
            #:equiv =α/racket
            t2
            (term (2 ((lambda (x) (1 x))))))
  (test-->> s-->βη
            #:equiv =α/racket
            t2
            (term (2 ((lambda (x) (1 x))))))
  
  (test--> s-->βη
           #:equiv =α/racket
           t3
           (term
            ((lambda (y z)
               ((lambda (a b) a) y z))
             1 2)))
  (test-->> s-->βη t3 1)

  (test-->  s-->β
            #:equiv =α/racket
            t2
            (term (2 ((lambda (x) (1 x))))))
  (test-->> s-->β
            #:equiv =α/racket
            t2
            (term (2 ((lambda (x) (1 x))))))
  
  (test--> s-->β
           #:equiv =α/racket
           t3
           (term
            ((lambda (y z)
               ((lambda (a b) a) y z))
             1 2)))
  (test-->> s-->β t3 1)
  #;
  (traces s-->βη t2))

(define s-->β
  (reduction-relation
   Lambda-η
   (--> (in-hole E ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole E (subst ([e_1 x_1] ...) e))
        β)))

(define s-->βη
  (extend-reduction-relation
   s-->β
   Lambda-η
   (--> (in-hole E (lambda (x ...) (e x ...)))
        (in-hole E e)
        η)
   (--> (in-hole E ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole E (subst ([e_1 x_1] ...) e))
        β)))

;; -----------------------------------------------------------------------------

(module+ test
  (test-equal (term (eval-β ,t2)) (term stuck))
  (test-equal (term (eval-β ,t3)) 1))

(define-metafunction Lambda-η
  eval-β : e -> v or closure or stuck 
  [(eval-β e) any_1 (where any_1 (run-β e))])

(define-metafunction Lambda-η
  run-β : e -> v or closure or stuck
  [(run-β n) n]
  [(run-β v) closure]
  [(run-β e)
   (run-β e_again)
   (where (e_again) ,(apply-reduction-relation s-->β (term e)))]
  [(run-β e) stuck])

;; -----------------------------------------------------------------------------

(module+ test
  (test-equal (term (eval-βη ,t2)) (term stuck))
  #;
  (traces s-->βη t3)
  (test-equal (term (eval-βη ,t3)) 1))

(define-metafunction Lambda-η
  eval-βη : e -> v or closure or stuck 
  [(eval-βη e) any_1 (where any_1 (run-βη e))])

(define-metafunction Lambda-η
  run-βη : e -> v or closure or stuck
  [(run-βη n) n]
  [(run-βη v) closure]
  [(run-βη e)
   (run-βη e_again)
   ;; this fix is needed because of α equivalent terms
   (where (e_again e_α ...) ,(apply-reduction-relation s-->βη (term e)))]
  [(run-βη e) stuck])

;; -----------------------------------------------------------------------------
;; Theorem eval-β = eval-βη

(module+ test
  (test-equal (term (theorem:eval-β=eval-βη t2)) #true)
  (test-equal (term (theorem:eval-β=eval-βη t3)) #true))

(define-metafunction Lambda-η
  theorem:eval-β=eval-βη : e -> boolean
  [(theorem:eval-β=eval-βη e) ,(equal? (term (eval-β e)) (term (eval-βη e)))])

(redex-check Lambda-η e (term (theorem:eval-β=eval-βη e)))
;; fails for bad terms (lambda (a a) a)

#| -----------------------------------------------------------------------------
;; exercise: add + to both by-name and by-value as a first-class function 

(define-extended-language Lambda-calculus/v+ Lambda-calculus/v
  (e ::= .... +)
  (v ::= .... +))

(module+ test
  (test-->> ->βv-+ (term ((lambda (x) (+ x 1)) 2)) 3)
  (test-->> ->βv-+ (term ((lambda (x) (x 2 1)) +)) 3)
  #;
  (traces ->βv-+ (term (+ (+ 1 1) 1)))
  (test-->> ->βv-+ (term (+ (+ 1 1) 1)) 3))

(define ->βv-+
  (extend-reduction-relation
   ->βv
   Lambda-calculus/v+
   (--> (in-hole C (+ n_1 n_2))
        (in-hole C ,(+ (term n_1) (term n_2))))))
|#

(module+ test
  (test-results))
