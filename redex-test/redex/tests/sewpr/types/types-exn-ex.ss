#lang scheme

(require redex "types-exn.ss")

;; ENDDEFS

;; EXAMPLE 1
(term (TC () ((λ X num X) 1)))
;; STOP 1

;; START stexn
(define (simply-typed? x)
  (with-handlers ((exn:fail:redex? (lambda (x) #f)))
    (term (TC () ,x))))
;; STOP stexn

(traces t-iswim-red
        (term (((λ x num (λ y num x)) 
                2)
               3))
        #:pred
        simply-typed?)

;; START traces-pred
(traces t-iswim-red
        (term (+ ((λ x num x) 1) 2))
        #:pred
        simply-typed?)
;; STOP traces-pred
