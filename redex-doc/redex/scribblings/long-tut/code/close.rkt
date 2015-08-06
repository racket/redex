#lang racket

;; a function that can close over the free variables of an expression

(provide
 ;; RACKET
 ;; [Any-> Boolean: valid expression] ->
 ;;      [Lambda.e #:init [i \x.x] -> Lambda.e]
 ;; ((close-over-fv-with lambda?) e) closes over all free variables in
 ;; a Lambda term (or sublanguage w/ no new binding constructs) by
 ;; binding them to (term (lambda (x) x))
 ;; ((close-over-fv-with lambda?) e #:init i)
 ;;       like above but binds free vars to i
 close-over-fv-with
 ;; any -> (x ...)
 ;; computes free variables of given term 
 fv)

(require redex "common.rkt")

;; -------------------------------------------------------
(module+ test
  ;; show two dozen terms
  (redex-check Lambda e #;displayln (term e)
               #:attempts 12
               #:prepare (close-over-fv-with lambda?))
  ;; see 0, can't work 
  #;
  (redex-check Lambda e #;displayln (term e)
               #:attempts 12
               #:prepare (λ (x) ((close-over-fv-with lambda?) x #:init 0))))

(define ((close-over-fv-with lambda?) e #:init (i (term (lambda (x) x))))
  ;; this is to work around a bug in redex-check; doesn't always work
  (if (lambda? e) (term (close ,e ,i)) i))

(define-metafunction Lambda
  close : any any -> any
  [(close any_1 any_2)
   (let ([x any_2] ...) any_1)
   (where (x ...) (unique (fv any_1)))])

(define-metafunction Lambda
  ;;  let : ((x e) ...) e -> e but e plus hole 
  let : ((x any) ...) any -> any
  [(let ([x_lhs any_rhs] ...) any_body)
   ((lambda (x_lhs ...) any_body) any_rhs ...)])

(define-metafunction Lambda
  unique : (x ...) -> (x ...)
  [(unique ()) ()]
  [(unique (x_1 x_2 ...))
   (unique (x_2 ...))
   (where #true (in x_1 (x_2 ...)))]
  [(unique (x_1 x_2 ...))
   (x_1 x_3 ...)
   (where (x_3 ...) (unique (x_2 ...)))])

;; -----------------------------------------------------------------------------
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
