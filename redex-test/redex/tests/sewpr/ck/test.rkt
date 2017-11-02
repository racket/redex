#lang racket/base
(require redex/reduction-semantics
         "ck.rkt"
         "iswim-test2.rkt"
         "../iswim/iswim.rkt")

(test-->> ck
          (term ((iszero 0) mt))
          (term ((λ x (λ y x)) mt)))
(test-->> ck
          (term ((iszero 1) mt))
          (term ((λ x (λ y y)) mt)))

(test-->> ck
          (term ((+ 1 2) mt))
          (term (3 mt)))
(test-->> ck
          (term (((λ x (+ x x)) 2) mt))
          (term (4 mt)))

(test-->> ck
          (term ((+ (+ 1 2) (+ 3 4)) mt))
          (term (10 mt)))

(test-->> ck
          (term (((((iszero 1)
                    (λ d 2))
                   (λ d 3))
                  0) 
                 mt))
          (term (3 mt)))
(test-->> ck
          (term (((((iszero 0)
                    (λ d 2))
                   (λ d 3))
                  0) 
                 mt))
          (term (2 mt)))

;; WRONG ANSWER!
(test-->> ck
          (term ((- (+ 1 2) (- 3 4)) mt))
          (term (-2 mt)))

;; make sure δ doesn't fire
(test-->> ck
          (term ((+ (λ x x) (λ y y)) mt))
          (term ((λ y y) (op ((λ x x) +) () mt))))


(test-->> ck-fix
          (term ((iszero 0) mt))
          (term ((λ x (λ y x)) mt)))
(test-->> ck-fix
          (term ((iszero 1) mt))
          (term ((λ x (λ y y)) mt)))

(test-->> ck-fix
          (term ((+ 1 2) mt))
          (term (3 mt)))
(test-->> ck-fix
          (term (((λ x (+ x x)) 2) mt))
          (term (4 mt)))

(test-->> ck-fix
          (term ((+ (+ 1 2) (+ 3 4)) mt))
          (term (10 mt)))

(test-->> ck-fix
          (term (((((iszero 1)
                    (λ d 2))
                   (λ d 3))
                  0) 
                 mt))
          (term (3 mt)))
(test-->> ck-fix
          (term (((((iszero 0)
                    (λ d 2))
                   (λ d 3))
                  0) 
                 mt))
          (term (2 mt)))

(test-->> ck-fix
          (term ((- (+ 1 2) (- 3 4)) mt))
          (term (4 mt)))

;; make sure δ doesn't fire
(test-->> ck-fix
          (term ((+ (λ x x) (λ y y)) mt))
          (term ((λ y y) (op ((λ x x) +) () mt))))

(test-predicate same-ck-stdred? (term (+ 1 2)))
(test-predicate same-ck-stdred? (term (((λ x (λ y (+ x y))) 1) 2)))
(test-equal (same-ck-stdred? (term ((λ x (- x 2)) 3))) #f)

(test-predicate same-fixed-answer? (term (+ 1 2)))
(test-predicate same-fixed-answer? (term (((λ x (λ y (+ x y))) 1) 2)))
(test-predicate same-fixed-answer? (term ((λ x (- x 2)) 3)))

(time (apply-reduction-relation* iswim-red big-example))
(time (apply-reduction-relation* ck (term (,big-example mt))))
