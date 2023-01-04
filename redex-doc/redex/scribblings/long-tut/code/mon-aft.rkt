#lang racket

#|
Lambda

;; constraints on languages (uniquesness, side conditions), key concepts (α)
unique-vars
in 
fv
 plus auxiliaries
=α
 plus auxiliaries 

Lambda/n: add numbers
 --> any because we want these functions to work or 'derived languages'

subst (if time, otherwise it's provide)
|#

(provide fv)

;; -----------------------------------------------------------------------------
(require redex)

(define-language Lambda
  (e ::=
     x 
     (lambda (x) e)
     (e e))
  (x ::= variable-not-otherwise-mentioned))

(define e1 (term y))
(define e2 (term (lambda (y) y)))
(define e3 (term (lambda (x) (lambda (y) y))))
(define e4 (term (,e2 ,e3)))

(define in-Lambda? (redex-match? Lambda e))

(module+ test
  (test-equal (in-Lambda? e1) #true)
  (test-equal (in-Lambda? e2) #true)
  (test-equal (in-Lambda? e3) #true)
  (test-equal (in-Lambda? e4) #true))

(define eb1 (term (lambda (y) (lambda () y))))
(define eb2 (term (lambda (x) (lambda (y) 3))))

(module+ test
  (test-equal (in-Lambda? eb1) #false)
  (test-equal (in-Lambda? eb2) #false))

;; -----------------------------------------------------------------------------
;; (unique-vars x ...) is the sequence of variables x ... free of duplicates?

(module+ test 
  (test-equal (term (unique-vars x y)) #true)
  (test-equal (term (unique-vars x y x)) #false))

(define-metafunction Lambda 
  unique-vars : x ... -> boolean 
  [(unique-vars) #true]
  [(unique-vars x x_1 ... x x_2 ...) #false]
  [(unique-vars x x_1 ...) (unique-vars x_1 ...)])

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
;; (fv e) computes the sequence of free variables of e

(module+ test
  (test-equal (term (fv x)) (term (x)))
  (test-equal (term (fv (lambda (x) x))) (term ()))
  (test-equal (term (fv (lambda (x) ((y z) x)))) (term (y z))))

(define-metafunction Lambda
  fv : e -> (x ...)
  [(fv x) (x)]
  [(fv (lambda (x) e_body))
   (subtract (x_e ...) x)
   (where (x_e ...) (fv e_body))]
  [(fv (e_f e_a))
   (x_f ... x_a ...)
   (where (x_f ...) (fv e_f))
   (where (x_a ...) (fv e_a))])

;; -----------------------------------------------------------------------------
;; (subtract (x ...) x_1 ...) removes x_1 ... from (x ...)

(module+ test
  (test-equal (term (subtract (x y z x) x z)) (term (y))))

(define-metafunction Lambda
  subtract : (x ...) x ... -> (x ...)
  [(subtract (x ...)) (x ...)]
  [(subtract (x ...) x_1 x_2 ...)
   (subtract (subtract1 (x ...) x_1) x_2 ...)])

(module+ test
  (test-equal (term (subtract1 (x y z x) x)) (term (y z))))

(define-metafunction Lambda
  subtract1 : (x ...) x -> (x ...)
  [(subtract1 (x_1 ... x x_2 ...) x)
   (x_1 ... x_2new ...)
   (where (x_2new ...) (subtract1 (x_2 ...) x))
   (where #false (in x (x_1 ...)))]
  [(subtract1 (x ...) x_1) (x ...)])


;; -----------------------------------------------------------------------------
;; (sd e) computes the static distance version of e

(define-extended-language SD Lambda
  (e ::= .... (K n) (lambda e) n)
  (n ::= natural))

(define sd1 (term (K 0)))

(define SD? (redex-match? SD e))

(module+ test
  (test-equal (SD? sd1) #true))

(define-metafunction SD
  sd : e -> e
  [(sd e) (sd/a e ())])

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
  sd/a : e (x ...) -> e
  [(sd/a x (x_1 ... x x_2 ...))
   ;; bound variable 
   (K n)
   (where n ,(length (term (x_1 ...))))
   (where #false (in x (x_1 ...)))]
  [(sd/a (lambda (x) e) (x_rest ...))
   (lambda (sd/a e (x x_rest ...)))
   (where n ,(length (term (x_rest ...))))]
  [(sd/a (e_fun e_arg) (x_rib ...))
   ((sd/a e_fun (x_rib ...)) (sd/a e_arg (x_rib ...)))]
  [(sd/a any_1 (x ...))
   ;; free variable or constant
   any_1])

;; -----------------------------------------------------------------------------
;; (=α e_1 e_2) determines whether e_1 and e_2 are α equivalent

(module+ test
  (test-equal (term (=α (lambda (x) x) (lambda (y) y))) #true)
  (test-equal (term (=α (lambda (x) (x z)) (lambda (y) (y z)))) #true)
  (test-equal (term (=α (lambda (x) x) (lambda (y) z))) #false))

(define-metafunction SD
  =α : e e -> boolean
  [(=α e_1 e_2) ,(equal? (term (sd e_1)) (term (sd e_2)))])

(define (=α/racket x y) (term (=α ,x ,y)))

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
              #:equiv =α/racket))

(define-metafunction Lambda
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x) any_body))
   (lambda (x_new)
     (subst ((any_1 x_1) ...)
            (subst-raw (x_new x) any_body)))
   (where  x_new ,(variable-not-in (term any_body) (term x)))]
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
