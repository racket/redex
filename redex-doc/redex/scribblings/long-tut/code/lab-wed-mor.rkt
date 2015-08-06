#lang racket

(require redex "wed-mor.rkt")

;; -----------------------------------------------------------------------------
;; (AV e) retrieves the sequence of left-hand side variables of assignments

(module+ test
  (test-equal (term (av ,e2)) (term (x y z))))

(define-metafunction Assignments
  av : e -> (x ...)
  [(av (lambda (x) e)) (av e)]
  [(av (e_1 e_2 ...))
   (x_1 ... x_2 ... ...)
   (where (x_1 ...) (av e_1))
   (where ((x_2 ...) ...) ((av e_2) ...))]
  [(av (set! x e))
   (x x_e ...)
   (where (x_e ...) (av e))]
  [(av (let ([x_lhs x_rhs]) e_1 e_2))
   (x_1 ... x_2 ...)
   (where (x_1 ...) (av e_1))
   (where (x_2 ...) (av e_2))]
  [(av any) ()])

(module+ test
  (test-results))
