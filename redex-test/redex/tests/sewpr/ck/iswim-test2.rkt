#lang racket/base
(require racket/list redex/reduction-semantics "../iswim/iswim.rkt")
(provide test-suite iswim-> abstract-test-suite same-answer? stdred-test-suite)

;; START suite
(define (test-suite)
  (test-->> iswim-red
            (term ((λ x (- x x)) 2))
            (term 4))
  (test-->> iswim-red
            (term ((λ x (+ x x)) 2))
            (term 4))
  (test-results))
;; STOP suite

;; START cal
(define-extended-language iswim-calculus 
  iswim 
  (C hole (M C) (C M) (o M ... C M ...) (λ X C)))

(define iswim-> 
  (reduction-relation
   iswim-calculus 
   (--> (in-hole C ((λ X M) V)) 
        (in-hole C (subst M X V)) βv)
   (--> (in-hole C (o b ...))
        (in-hole C (δ (o b ...))) δ)))
;; STOP cal


;; START abs 
(define (abstract-test-suite rr label)
  (printf "testing ~a\n" label)
  (test-->> rr 
            (term ((λ x (+ x x)) 2))
            (term 4))
  (test-->> rr 
            (term ((λ x (- x x)) 2))
            (term 0))
  (test-results))
;; STOP abs

;; START same
(define (same-answer? exp)
  (define calculus-answers
    (apply-reduction-relation* iswim-> exp))
  (define stdred-answers
    (apply-reduction-relation* iswim-red exp))
  (and (equal? (length calculus-answers) 1)
       (equal? (length stdred-answers) 1)
       (equal? (first calculus-answers)
               (first stdred-answers))))
;; STOP same 

;; START same2
(define (stdred-test-suite)
  (test-predicate same-answer? (term ((λ x (- x x)) 2)))
  (test-predicate same-answer? (term ((λ x (+ x x)) 2)))
  (test-results))
;; STOP same2
