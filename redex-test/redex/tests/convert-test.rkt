#lang racket
(require "private/bitmap-test-util.rkt"
         redex/pict redex/reduction-semantics
         pict
         pict/convert
         rackunit)


(define (pict-same? p1 p2)
  (bitmaps-same? (pict->bitmap p1) (pict->bitmap p2)))


(struct pict2 (pict)
  #:property prop:pict-convertible
  (lambda (x) (pict2-pict x)))

(define lift? (make-parameter #f))
(define (lift p)
  (if (lift?)
      (pict2 p)
      p))

(define-check (test f)
  (check-true
   (pict-same?
    (parameterize ([lift? #f]) (f))
    (parameterize ([lift? #t]) (f)))))


(define-language L
  (n ::= naturals)
  (e ::= n (+ e e))
  (H ::= hole
     (+ n H)
     (+ H e)))

(define R
  (reduction-relation
   L
   #:domain e
   (--> (in-hole H (+ n_1 n_2))
        (in-hole H (plus n_1 n_2)))))

(define-metafunction L
  plus : n n -> n
  [(plus n_1 n_2)
   ,(+ (term n_1) (term n_2))])
(define plus-rw
  (lambda (lws)
      (list ""
            (lift (text "⌈" (default-style) (default-font-size)))
            (list-ref lws 3)
            (lift (text "+" (default-style) (default-font-size)))
            (list-ref lws 4)
            (lift (text "⌉" (default-style) (default-font-size))))))

(define (with-renderers f)
  (parameterize ([white-square-bracket
                  (lambda (x) (lift (homemade-white-square-bracket x)))])
    (with-compound-rewriters
     (['plus plus-rw])
     (with-atomic-rewriters
      (['n (lambda () (lift (text "𝕟" (default-style) (default-font-size))))])
      (f)))))

(test
 (lambda ()
   (with-renderers
    (lambda () (render-language L)))))


(test
 (lambda ()
   (with-renderers
    (lambda () (render-metafunction plus #:contract? #t)))))

(test
 (lambda ()
   (with-renderers
    (lambda () (render-reduction-relation R)))))