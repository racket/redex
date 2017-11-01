#lang racket/base

#|

Like iswim.rkt, this file is required by other files, so 
all of the evaluation that prints, etc is moved to
eiswim-test.rkt

|#

(require redex/reduction-semantics "../iswim/iswim.rkt")

(provide e-iswim δ/ e-iswim-red-first-try e-iswim-red e-iswim-red2)

;; START lang
(define-extended-language e-iswim
  iswim
  (M .... 
     (err b))
  (o2 ....
      /))
;; STOP lang

;; START lang-alt
(define-language e-iswim-full
  ((M N L K) X (λ X M) (M M) b (o2 M M) (o1 M) (err b))
  (o o1 o2)
  (o1 add1 sub1 iszero)
  (o2 + - * ↑ /)
  (b number)
  ((V U W) b X (λ X M))
  (E hole (V E) (E M) (o V ... E M ...))
  ((X Y Z) variable-not-otherwise-mentioned))
;; STOP lang-alt

;; START delta
(define-metafunction e-iswim
  [(δ/ (/ b 0)) (err 0)]
  [(δ/ (/ b_1 b_2)) ,(/ (term b_1) (term b_2))]
  [(δ/ (o V ...)) (δ (o V ...))])
;; STOP delta

;; START red1
(define e-iswim-red-first-try
  (extend-reduction-relation
   iswim-red
   e-iswim
   (--> (in-hole E (o b ...))
        (in-hole E (δ/ (o b ...)))
        δ)
   (--> (in-hole E (o b ... (λ X M) V ...))
        (in-hole E (err ,(add1 (length (term (b ...))))))
        δerr1)
   (--> (in-hole E (b V))
        (in-hole E (err b))
        δerr2)
   (--> (in-hole E (err b))
        (err b)
        err)))
;; STOP red1

;; START red
(define e-iswim-red 
  (extend-reduction-relation
   iswim-red
   e-iswim
   (--> (in-hole E (o b ...))
        (in-hole E (δ/ (o b ...)))
        δ)
   (--> (in-hole E (o b ... (λ X M) V ...))
        (in-hole E (err ,(add1 (length (term (b ...))))))
        δerr1)
   (--> (in-hole E (b V))
        (in-hole E (err b))
        δerr2)
   (--> (in-hole E (err b))
        (err b)
        err
        (side-condition
         (not (equal? (term hole) (term E)))))))
;; STOP red

;; START red2
(define e-iswim-red2
  (reduction-relation
   e-iswim
   (ē ((λ X M) V) (subst M X V) βv)
   (ē (o b ...) (δ/ (o b ...)) δ)
   (ē (o b ... (λ X M) V ...)
      (err ,(add1 (length (term (b ...)))))
      δerr1)
   (ē (b V) (err b) δerr2)
   (--> (in-hole E (err b))
        (err b)
        (side-condition 
         (not (equal? (term E) (term hole)))))
   with
   ;; ORIGINAL
   ;;; [(--> (in-hole E a) (in-hole E b)) (ē a b)]))
   ;; ERRATA from https://github.com/racket/redex/commit/cbb2d88b98fb814325f0d4ee468e1abaf4f6c3a7 on Dec 12, 2015 --- needed for v6.4+
   [(--> (in-hole E x) (in-hole E y)) (ē x y)]))
;; STOP red2
