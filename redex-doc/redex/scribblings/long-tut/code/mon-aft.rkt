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

(define-language Lambda0
  (e ::=
     x 
     (lambda (x ...) e)
     (e e ...))
  (x ::= variable-not-otherwise-mentioned))

(define-language Lambda-bad
  (e ::=
     x 
     (side-condition (lambda (x_ ...) e) (term (unique-vars (x_ ...))))
     (e e ...))
  (x ::= variable-not-otherwise-mentioned))

(define-language Lambda
  (e ::=
     x 
     (lambda (x_!_ ...) e)
     (e e ...))
  (x ::= variable-not-otherwise-mentioned))

(define e1 (term y))
(define e2 (term (lambda (y) y)))
(define e3 (term (lambda (x y) y)))
(define e4 (term (,e2 e3)))

(define in-Lambda? (redex-match? Lambda e))

(module+ test
  (test-equal (in-Lambda? e1) #true)
  (test-equal (in-Lambda? e2) #true)
  (test-equal (in-Lambda? e3) #true)
  (test-equal (in-Lambda? e4) #true))

(define eb1 (term (lambda (x x) y)))
(define eb2 (term (lambda (x y) 3)))

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
  (test-equal (term (fv (lambda (x) (y z x)))) (term (y z))))

(define-metafunction Lambda
  fv : any -> (x ...)
  [(fv x) (x)]
  [(fv (lambda (x ...) any_body))
   (subtract (x_e ...) x ...)
   (where (x_e ...) (fv any_body))]
  [(fv (any_f any_a ...))
   (x_f ... x_a ... ...)
   (where (x_f ...) (fv any_f))
   (where ((x_a ...) ...) ((fv any_a) ...))]
  [(fv any) ()])

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
  (e ::= .... (K n n) (lambda n e))
  (n ::= natural))

(define sd1 (term (K 0 1)))
(define sd2 (term 1))

(define SD? (redex-match? SD e))

(module+ test
  (test-equal (SD? sd1) #true))

(define-metafunction SD
  sd : any -> any
  [(sd any_1) (sd/a any_1 ())])

(module+ test
  (test-equal (term (sd/a x ())) (term x))
  (test-equal (term (sd/a x ((y) (z) (x)))) (term (K 2 0)))
  (test-equal (term (sd/a ((lambda (x) x) (lambda (y) y)) ()))
              (term ((lambda 1 (K 0 0)) (lambda 1 (K 0 0)))))
  (test-equal (term (sd/a (lambda (x) (x (lambda (y) y))) ()))
              (term (lambda 1 ((K 0 0) (lambda 1 (K 0 0))))))
  (test-equal (term (sd/a (lambda (z x) (x (lambda (y) z))) ()))
              (term (lambda 2 ((K 0 1) (lambda 1 (K 1 0)))))))

(define-metafunction SD
  sd/a : any ((x ...) ...) -> any
  [(sd/a x ((x_1 ...) ... (x_0 ... x x_2 ...) (x_3 ...) ...))
   ;; bound variable 
   (K n_rib n_pos)
   (where n_rib ,(length (term ((x_1 ...) ...))))
   (where n_pos ,(length (term (x_0 ...))))
   (where #false (in x (x_1 ... ...)))]
  [(sd/a (lambda (x ...) any_1) (any_rest ...))
   (lambda n (sd/a any_1 ((x ...) any_rest ...)))
   (where n ,(length (term (x ...))))]
  [(sd/a (any_fun any_arg ...) (any_rib ...))
   ((sd/a any_fun (any_rib ...)) (sd/a any_arg (any_rib ...)) ...)]
  [(sd/a any_1 any)
   ;; free variable, constant, etc 
   any_1])

;; -----------------------------------------------------------------------------
;; (=α e_1 e_2) determines whether e_1 and e_2 are α equivalent

(define-extended-language Lambda/n Lambda
  (e ::= .... n)
  (n ::= natural))

(define in-Lambda/n? (redex-match? Lambda/n e))

(module+ test
  (test-equal (term (=α (lambda (x) x) (lambda (y) y))) #true)
  (test-equal (term (=α (lambda (x) (x 1)) (lambda (y) (y 1)))) #true)
  (test-equal (term (=α (lambda (x) x) (lambda (y) z))) #false))

(define-metafunction SD
  =α : any any -> boolean
  [(=α any_1 any_2) ,(equal? (term (sd any_1)) (term (sd any_2)))])

(define (=α/racket x y) (term (=α ,x ,y)))

;; -----------------------------------------------------------------------------
;; (subst ([e x] ...) e_*) substitutes e ... for x ... in e_* (hygienically)

(module+ test
  (test-equal (term (subst ([1 x][2 y]) x)) 1)
  (test-equal (term (subst ([1 x][2 y]) y)) 2)
  (test-equal (term (subst ([1 x][2 y]) z)) (term z))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z w) (x y))))
              (term (lambda (z w) (1 2))))
  (test-equal (term (subst ([1 x][2 y]) (lambda (z w) (lambda (x) (x y)))))
              (term (lambda (z w) (lambda (x) (x 2))))
              #:equiv =α/racket)
  (test-equal (term (subst ((2 x)) ((lambda (x) (1 x)) x)))
              (term ((lambda (x) (1 x)) 2))
              #:equiv =α/racket))
              
              

(define-metafunction Lambda
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x ...) any_body))
   (lambda (x_new ...)
     (subst ((any_1 x_1) ...)
            (subst-raw ((x_new x) ...) any_body)))
   (where  (x_new ...)  ,(variables-not-in (term any_body) (term (x ...)))) ]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])

(define-metafunction Lambda
  subst-raw : ((x x) ...) any -> any
  [(subst-raw ((x_n1 x_o1) ... (x_new x) (x_n2 x_o2) ...) x) x_new]
  [(subst-raw ((x_n1 x_o1) ... ) x) x]
  [(subst-raw ((x_n1 x_o1) ... ) (lambda (x ...) any))
   (lambda (x ...) (subst-raw ((x_n1 x_o1) ... ) any))]
  [(subst-raw [(any_1 x_1) ... ] (any ...))
   ((subst-raw [(any_1 x_1) ... ] any) ...)]
  [(subst-raw [(any_1 x_1) ... ] any_*) any_*])

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
