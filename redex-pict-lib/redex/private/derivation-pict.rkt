#lang racket/base
(require "derivations-layout.rkt"
         "pict.rkt"
         racket/class
         racket/contract
         texpict/mrpict)
(provide derivation->pict)

(define derivation-element%
  (class object%
    (super-new)
    (init term label)
    (init-field children)
    (define t (term->pict/pretty-write (current-lang) term))
    (define n (if label (string->bracketed-label label) (blank 0 0)))
    (define tx 0)
    (define ty 0)
    (define nx 0)
    (define ny 0)
    (define lx 0)
    (define ly 0)
    (define lw 0)
    (define/public (get-term-size)
      (values (pict-width t)
              (pict-height t)))
    (define/public (get-name-size)
      (values (pict-width n)
              (pict-height n)))
    (define/public (set-term-position x y) (set! tx x) (set! ty y))
    (define/public (set-name-position x y) (set! nx x) (set! ny y))
    (define/public (set-line-layout x y w) (set! lx x) (set! ly y) (set! lw w))
    (define/public (get-children) children)
    (define/public (add-elements p0)
      (define pl (pin-over p0 lx ly (frame (blank lw 0))))
      (define pn (if n (pin-over pl nx ny n) pl))
      (define pt (pin-over pn tx ty t))
      pt)
    (define/public (get-bottom-right)
      (values (max (+ lx lw)
                   (+ tx (pict-width t))
                   (if n (+ nx (pict-width n)) 0))
              (max ly
                   (+ ty (pict-height t))
                   (if n (+ ny (pict-height n)) 0))))))

(define pict-container%
  (class object%
    (define root #f)
    
    (define/public (add-node term label children)
      (new derivation-element% [term term] [label label] [children children]))
    (define/public (set-root r) (set! root r))
    (define/public (get-root) root)
    (define/public (get-size) (values 0 0))
    (define/public (get-pict)
      (define w 0)
      (define h 0)
      (let loop ([p root])
        (define-values (tw th) (send p get-bottom-right))
        (set! w (max w tw))
        (set! h (max h th))
        (for ([c (in-list (send p get-children))])
          (loop c)))
      (define b (blank w h))
      (let loop ([p root])
        (set! b (send p add-elements b))
        (for ([c (in-list (send p get-children))])
          (loop c)))
      b)
    (super-new)))

(define (derivation->pict L derivation)
  (define container (new pict-container%))
  (parameterize ([current-lang L])
    (fill-derivation-container container derivation))
  (layout-derivation container)
  (send container get-pict))

(define current-lang (make-parameter #f))
