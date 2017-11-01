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

(define-syntax-rule 
  (capture-output arg1 args ...)
  (let ([p (open-output-string)])
    (parameterize ([current-output-port p]
                   [current-error-port p])
      arg1 args ...)
    (get-output-string p)))

(test-results) ;; we have to clear out the results here to be able to run the next few test cases

(test-equal (and (regexp-match
                  #rx"1 test failed \\(out of 2 total\\)"
                  (capture-output (test-suite)))
                 #t)
            #t)
(test-results) ;; each of these tests has to clear the results

(test-equal (and (regexp-match
                  #rx"Both tests passed."
                  (capture-output (abstract-test-suite iswim-red 'iswim-red)))
                 #t)
            #t)
(test-results)

(test-equal (and (regexp-match 
                  #rx"Both tests passed."
                  (capture-output (abstract-test-suite iswim-> 'iswim->)))
                 #t)
            #t)
(test-results)

(test-equal (and (regexp-match 
                  #rx"Both tests passed."
                  (capture-output (stdred-test-suite)))
                 #t)
            #t)
(test-results)

;; generates the traces from section 3
; (traces ck (term (((λ x (- x 1)) 2) mt)))

(time (apply-reduction-relation* iswim-red big-example))
(time (apply-reduction-relation* ck (term (,big-example mt))))
