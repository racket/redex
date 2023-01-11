#lang racket

;; basic definitions for the Redex Summer School 2015

(provide
 ;; Language 
 Lambda
 
 ;; Any -> Boolean
 ;; is the given value in the expression language? 
 lambda?
 
 ;; x (x ...) -> Boolean
 ;; (in x (x_1 ...)) determines whether x occurs in x_1 ...
 in
 
 ;; Any Any -> Boolean
 ;; (=α/racket e_1 e_2) determines whether e_1 is α-equivalent to e_2
 ;; e_1, e_2 are in Lambda or extensions of Lambda that 
 ;; do not introduce binding constructs beyond lambda 
 =α/racket
 
 ;; ((Lambda x) ...) Lambda -> Lambda
 ;; (subs ((e_1 x_1) ...) e) substitures e_1 for x_1 ... in e
 ;; e_1, ... e are in Lambda or extensions of Lambda that 
 ;; do not introduce binding constructs beyond lambda 
 subst)

;; -----------------------------------------------------------------------------
(require redex)

(define-language Lambda
  (e ::=
     x 
     (lambda (x) e)
     (e e))
  (x ::= variable-not-otherwise-mentioned))

(define lambda? (redex-match? Lambda e))

(module+ test
  (define e1 (term y))
  (define e2 (term (lambda (y) y)))
  (define e3 (term (lambda (x) (lambda (y) y))))
  (define e4 (term (,e2 e3)))

  (test-equal (lambda? e1) #true)
  (test-equal (lambda? e2) #true)
  (test-equal (lambda? e3) #true)
  (test-equal (lambda? e4) #true)

  (define eb1 (term (lambda () y)))
  (define eb2 (term (lambda (x) (lambda (y) 3))))

  (test-equal (lambda? eb1) #false)
  (test-equal (lambda? eb2) #false))

;; -----------------------------------------------------------------------------
;; (in x x_1 ...) is x a member of (x_1 ...)?

(module+ test
  (test-equal (term (in x (y z x y z))) #true)
  (test-equal (term (in x ())) #false)
  (test-equal (term (in x (y z w))) #false))

(define-metafunction Lambda
  in : x (x ...) -> boolean
  [(in x (x_1 ... x x_2 ...)) #true]
  [(in x (x_1 ...)) #false])

;; -----------------------------------------------------------------------------
;; (=α e_1 e_2) determines whether e_1 and e_2 are α equivalent

(module+ test
  (test-equal (term (=α (lambda (x) x) (lambda (y) y))) #true)
  (test-equal (term (=α (lambda (x) (x 1)) (lambda (y) (y 1)))) #true)
  (test-equal (term (=α (lambda (x) x) (lambda (y) z))) #false)
  (test-equal (term (=α (lambda (x) x) (lambda (x) (lambda (x) x)))) #false)
  (test-equal (term (=α (lambda (x) x) (lambda (x) (x x)))) #false)
  (test-equal (term (=α (lambda (x) (lambda (y) (x y))) (lambda (x) (lambda (y) (y x))))) #false)
  (test-equal (term (=α (lambda (x) (lambda (y) (x y))) (lambda (a) (lambda (b) (a b))))) #true))

(define-metafunction Lambda
  =α : any any -> boolean
  [(=α any_1 any_2) ,(equal? (term (sd any_1)) (term (sd any_2)))])

;; a Racket definition for use in Racket positions 
(define (=α/racket x y) (term (=α ,x ,y)))

;; (sd e) computes the static distance version of e
(define-extended-language SD Lambda
  (e ::= .... (K n) (lambda e))
  (n ::= natural))

(define SD? (redex-match? SD e))

(module+ test
  (define sd1 (term (K 1)))

  (test-equal (SD? sd1) #true))

(define-metafunction SD
  sd : any -> any
  [(sd any) (sd/a any ())])

(module+ test
  (test-equal (term (sd/a x ())) (term x))
  (test-equal (term (sd/a x (y z x))) (term (K 2)))
  (test-equal (term (sd/a ((lambda (x) x) (lambda (y) y)) ()))
              (term ((lambda (K 0)) (lambda (K 0)))))
  (test-equal (term (sd/a (lambda (x) (x (lambda (y) y))) ()))
              (term (lambda ((K 0) (lambda (K 0))))))
  (test-equal (term (sd/a (lambda (z) (lambda (x) (x (lambda (y) z)))) ()))
              (term (lambda (lambda ((K 0) (lambda (K 2))))))))

(define-metafunction SD
  sd/a : any (x ...) -> any
  [(sd/a x (x_1 ... x x_2 ...))
   ;; bound variable 
   (K n)
   (where n ,(length (term (x_1 ...))))
   (where #false (in x (x_1 ...)))]
  [(sd/a (lambda (x) any_body) (x_rest ...))
   (lambda (sd/a any_body (x x_rest ...)))
   (where n ,(length (term (x_rest ...))))]
  [(sd/a (any_fun any_arg) (x_rib ...))
   ((sd/a any_fun (x_rib ...)) (sd/a any_arg (x_rib ...)))]
  [(sd/a any_1 (x ...))
   ;; free variable or constant, etc
   any_1])


;; -----------------------------------------------------------------------------
;; (subst ([e x] ...) e_*) substitutes e ... for x ... in e_* (hygienically)

(module+ test
  (test-equal (term (subst ([1 x][2 y]) x)) 1)
  (test-equal (term (subst ([1 x][2 y]) y)) 2)
  (test-equal (term (subst ([1 x][2 y]) z)) (term z))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z) (lambda (w) (x y)))))
              (term (lambda (z) (lambda (w) (1 2)))))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z) (lambda (w) (lambda (x) (x y))))))
              (term (lambda (z) (lambda (w) (lambda (x) (x 2)))))
              #:equiv =α/racket)
  (test-equal (term (subst ((2 x)) ((lambda (x) (1 x)) x)))
              (term ((lambda (x) (1 x)) 2))
              #:equiv =α/racket)
  (test-equal (term (subst (((lambda (x) y) x)) (lambda (y) x)))
              (term (lambda (y1) (lambda (x) y)))
              #:equiv =α/racket))

(define-metafunction Lambda
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x) any_body))
   (lambda (x_new)
     (subst ((any_1 x_1) ...)
            (subst-raw (x_new x) any_body)))
   (where  x_new ,(variable-not-in (term (any_body any_1 ...)) (term x)))]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])

(define-metafunction Lambda
  subst-raw : (x x) any -> any
  [(subst-raw (x_new x_) x_) x_new]
  [(subst-raw (x_new x_) x) x]
  [(subst-raw (x_new x_) (lambda (x) any))
   (lambda (x) (subst-raw (x_new x_) any))]
  [(subst-raw (x_new x_) (any ...))
   ((subst-raw (x_new x_) any) ...)]
  [(subst-raw (x_new x_) any_*) any_*])

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
