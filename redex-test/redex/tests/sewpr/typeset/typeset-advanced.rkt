#lang scheme
(require "../iswim/iswim.rkt")
(require redex)
(require slideshow/pict scheme/class)

;; START subst-rw
;; subst-rw : (Listof lw) -> (Listof (U String lw))
(define (subst-rw lws)
  (list ""
        (list-ref lws 2)
        "{"
        (list-ref lws 3)
        ":="
        (list-ref lws 4)
        "}"))
;; STOP subst-rw

#|
A neat idea, but not needed and too much work to explain.

(define (blb) (mk-gb 1 -1 cb-superimpose))
(define (brb) (mk-gb -1 -1 cb-superimpose))
(define (tlb) (mk-gb 1 1 ct-superimpose))
(define (trb) (mk-gb -1 1 ct-superimpose))

(define (mk-gb mx my superimpose)
  (let ([base (ghost (text "I"))])
    (refocus 
     (superimpose
      base
      (dc
       (λ (dc dx dy)
         (send dc draw-line
               dx (+ dy (* my 1))
               dx (+ dy (* my 4)))
         (send dc draw-line 
               dx (+ dy (* my 1))
               (+ dx (* mx 3)) (+ dy (* my 1))))
       0 0 0 0))
     base)))
|#

(define (rewrite-lst.v1 eles)
  (define hd (lw-e (list-ref eles 1)))
  (define a1 (list-ref (lw-e (list-ref eles 2)) 2))
  (define rst 
    (if (<= (length eles) 4)
        '()
        (list 'spring 
              (list-ref (lw-e (list-ref eles 3)) 2))))
  (cond
    [(eq? hd 'add1)
     (list a1 (just-after "+1" a1))]
    [(eq? hd 'sub1)
     (list a1 (just-after "–1" a1))]
    [(eq? hd '+)
     (cons a1 (cons (just-after "+" a1) rst))]
    [(eq? hd '-)
     (cons a1 (cons (just-after "–" a1) rst))]
    [(eq? hd 'expt)
     (cons a1 (cons (just-after "^" a1) rst))]
    [(eq? hd '*)
     (cons a1 rst)]))

;; START rewrite-uq
;; rewrite-uq : lw -> lw
;; copy the given instance, rewrite e via rewrite-lst
(define (rewrite-uq a-lw)
  (struct-copy lw 
               a-lw
               [e (rewrite-lst (lw-e a-lw))]
               [unq? #f]))

;; rewrite-lst : (Listof lw) -> (Listof lw)
;; rewrite the parse tree of an escaping expression
(define (rewrite-lst eles)
  (define hd (lw-e (list-ref eles 1)))
  (define a1 (list-ref (lw-e (list-ref eles 2)) 2))
  (define rst 
    (if (<= (length eles) 4)
        '()
        (list 'spring 
              (list-ref (lw-e (list-ref eles 3)) 2))))
  (case hd
    [(add1) (list a1 (just-after "+1" a1))]
    [(sub1) (list a1 (just-after "–1" a1))]
    [(+)    (cons a1 (cons (just-after "+" a1) rst))]
    [(-)    (cons a1 (cons (just-after "–" a1) rst))]
    [(expt) (cons a1 (cons (just-after "^" a1) rst))]
    [(*)    (cons a1 rst)]))
;; STOP rewrite-uq

(define (rewrite-uq/exponent a-lw)
  (let ([hd (lw-e (list-ref (lw-e a-lw) 1))])
    (struct-copy lw
                 a-lw
                 [e (rewrite-lst/exponent hd (lw-e a-lw))]
                 [unq? #f])))

(define (rewrite-lst/expt.v0 hd eles)
  (let ([arg1 (list-ref (lw-e (list-ref eles 2)) 2)])
    (cond
      [(eq? hd 'add1)
       (list arg1 (just-after "+1" arg1))]
      [(eq? hd 'sub1)
       (list arg1 (just-after "–1" arg1))]
      [else
       (let ([arg2 (list-ref (lw-e (list-ref eles 3)) 2)])
         (cond
           [(eq? hd '+)
            (list arg1 (just-after "+" arg1) 'spring arg2)]
           [(eq? hd '-)
            (list arg1 (just-after "–" arg1) 'spring arg2)]
           ;; START rewrite-lst2
           [(eq? hd 'expt)
            (list arg1 
                  'spring 
                  (exponent arg2))]
           ;; STOP rewrite-lst2
           [(eq? hd '*)
            (list arg1 'spring arg2)]))])))

(define (rewrite-lst/exponent hd eles)
    (define hd (lw-e (list-ref eles 1)))
  (define a1 (list-ref (lw-e (list-ref eles 2)) 2))
  (define rst 
    (if (<= (length eles) 4)
        '()
        (list 'spring 
              (list-ref (lw-e (list-ref eles 3)) 2))))
  (case hd
    [(add1) (list a1 (just-after "+1" a1))]
    [(sub1) (list a1 (just-after "–1" a1))]
    [(+)    (cons a1 (cons (just-after "+" a1) rst))]
    [(-)    (cons a1 (cons (just-after "–" a1) rst))]
    ;; START rewrite-lst2
    [(expt) (list (just-after (exponent) a1))]
    ;; STOP rewrite-lst2
    [(*)    (cons a1 rst)]))

;; START rewrite-lst2b
;; exponent : -> pict
;; create a pict for the exponent of b_1 to the b_2
(define (exponent)
  (define b 
    (text "b" (non-terminal-style)))
  (define one
    (text "1" (non-terminal-subscript-style)))
  (define b2
    (hbl-append
     (text "b" (non-terminal-style))
     (text "2" (non-terminal-subscript-style))))
  (define lifted-b2
    (drop-below-ascent (scale b2 .7) -6))
  (hbl-append b (lbl-superimpose lifted-b2 one)))
;; STOP rewrite-lst2b

;; ENDDEFS

;; EXAMPLE red-rw
(with-compound-rewriter 'subst subst-rw
 (render-reduction-relation 
  iswim-red #:style 'horizontal))
;; STOP red-rw

;; EXAMPLE mf2
(with-unquote-rewriter rewrite-uq
                       (render-metafunction δ))
;; STOP mf2

;; EXAMPLE mf3
(with-unquote-rewriter rewrite-uq/exponent
                       (render-metafunction δ))
;; STOP mf3
