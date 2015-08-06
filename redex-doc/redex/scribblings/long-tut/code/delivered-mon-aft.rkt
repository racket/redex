#lang racket
(require redex)

;; developing a language model 
;; 1. define a syntax 
;; 2. define examples
;; 3. impose constraints
;; -------- write down membeship tests 
;; 4. free variables 
;; 5. α
;; 6. substitution 

(define-language Lambda
  (e ::=
     x 
     (lambda (x_!_ ...) e)
     (e e ...))
  (x ::= variable-not-otherwise-mentioned))

(define e1 (term (lambda (x) (lambda (y) (y x)))))
(define e2 (term (lambda (x) (x x))))
(define e3 (term (,e2 ,e2)))

(define e4 (term (lambda (z z) z)))

(module+ test 
  (test-equal (redex-match? Lambda e e1) #t)
  (test-equal (redex-match? Lambda e e2) #t)
  (test-equal (redex-match? Lambda e e3) #t)
  (test-equal (redex-match? Lambda e e4) #f))

;; -----------------------------------------------------------------------------
;; (in x (x_1 ...)) determines whether x occurs in x_1 ...

(module+ test
  (test-equal (term (in a (b c a d a))) #t)
  (test-equal (term (in z (b c a d a))) #f))

(define-metafunction Lambda
  in : x (x_1 ...) -> boolean
  [(in x (x_1 ... x x_2 ...)) #true]
  [(in _ _) #false])

;; -----------------------------------------------------------------------------
(define-extended-language SD Lambda
  (e ::= .... (K n n) (lambda n e))
  (n ::= natural))

;; (=α e_1 e_2) determines whether e_1 is equal to e_2 modulo bound names

(module+ test
  (test-equal (term (=α (lambda (a) a) (lambda (b) b))) #true)
  (test-equal (term (=α (lambda (a) (lambda (c) (c a)))
                        (lambda (b) (lambda (z) (z b))))) #true))

(define-metafunction SD
  =α : any any -> boolean
  [(=α any_1 any_2) ,(equal? (term (sd any_1)) (term (sd any_2)))])

(define (=α/racket x y) (term (=α ,x ,y)))

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

(define-extended-language Lambda-with-numbers Lambda
  (e ::= .... n (+ e e))
  (n ::= number))


(define e17 (term (5 (lambda (x y) (+ x 42)))))
(define e19 (term (5 (lambda (sarah jeff) (+ sarah 42)))))

(module+ test
  (test-equal (redex-match? Lambda e e17) #false)
  (test-equal (redex-match? Lambda-with-numbers e e17) #true)
  (test-equal (redex-match? Lambda-with-numbers e e19) #true))

(term (=α ,e17 ,e19))

(module+ test
  (test-results))