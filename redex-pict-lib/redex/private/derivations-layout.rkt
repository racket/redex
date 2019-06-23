#lang racket/base
(require racket/class
         racket/match
         racket/contract
         redex/private/lang-struct
         racket/dict)

(provide
 (contract-out
  [fill-derivation-container (-> derivation-container/c derivation? void?)]
  [layout-derivation (-> derivation-container/c void?)]))

(define derivation-element/c
  (object/c
   [get-term-size (->m (values (>=/c 0) (>=/c 0)))]
   [get-name-size  (->m (values (or/c #f (>=/c 0)) (or/c #f (>=/c 0))))]
   [set-term-position (->m real? real? void?)]
   [set-name-position (->m real? real? void?)]
   [set-line-layout (->m real? real? (>=/c 0) void?)]
   [get-children  (->m (listof (recursive-contract derivation-element/c)))]))

(define derivation-container/c
  (object/c
   [add-node (->m any/c (or/c string? #f) (listof derivation-element/c) derivation-element/c)]
   [set-root (->m derivation-element/c void?)]
   [get-root (->m (or/c #f derivation-element/c))]
   [get-size (->m (values (or/c #f (>=/c 0)) (or/c #f (>=/c 0))))]))

(define sub-derivation-horizontal-gap 20)
(define sub-derivation-vertical-gap 10) ;; must be even

(define (fill-derivation-container derivation-container derivation)
  (define root-derivation-element
    (let loop ([derivation derivation])
      (define children
        (reverse
         (for/fold ([children '()])
                   ([sub (in-list (derivation-subs derivation))])
           (cons (loop sub) children))))
      (send derivation-container add-node
            (derivation-term derivation)
            (derivation-name derivation)
            children)))
  (send derivation-container set-root root-derivation-element))

(define (layout-derivation derivations-container)
  (define top-snip (send derivations-container get-root))
  (define table (resize-derivation derivations-container))
  (define-values (w h) (send derivations-container get-size))
  (define-values (init-x init-y)
    (cond
      [(and w h)
       (match-define (cons derivation-width derivation-height) (dict-ref table top-snip))
       (values (max 0 (- (/ w 2) (/ derivation-width 2)))
               (max 0 (- (/ h 2) (/ derivation-height 2))))]
      [else
       (values 0 0)]))
  (place-derivation table derivations-container init-x init-y))

(define (place-derivation table derivations-container dx dy)
  (define root (send derivations-container get-root))
  (unless root (error 'layout-derivation "root not yet set"))
  (let loop ([dx dx] [dy dy] [derivation-element root])
    (match-define (cons derivation-width derivation-height)
      (dict-ref table derivation-element))
    (define-values (my-width my-height) (send derivation-element get-term-size))
    (define-values (name-snip-width/f name-snip-height/f) (send derivation-element get-name-size))
    (define name-snip-width (or name-snip-width/f 0))
    (define my-x (+ dx (- (/ (- derivation-width name-snip-width) 2) (/ my-width 2))))
    (define my-y (+ dy derivation-height (- my-height)))
    (send derivation-element set-term-position my-x my-y)
    (define children-width
      (for/sum ([child (in-list (send derivation-element get-children))])
        (match-define (cons cw ch) (dict-ref table child))
        cw))
    (define start-dx (+ dx (/ (- (- derivation-width name-snip-width) children-width) 2)))
    (send derivation-element set-line-layout
          dx
          (- my-y (/ sub-derivation-vertical-gap 2))
          (- derivation-width name-snip-width))
    (when name-snip-width/f
      (send derivation-element set-name-position
            (+ dx derivation-width (- name-snip-width))
            (- my-y (/ sub-derivation-vertical-gap 2) (/ name-snip-height/f 2))))
    (for/fold ([dx start-dx]) ([snip (in-list (send derivation-element get-children))])
      (match-define (cons that-ones-width that-ones-height) (dict-ref table snip))
      (loop dx
            (+ dy (- derivation-height that-ones-height my-height sub-derivation-vertical-gap))
            snip)
      (+ dx that-ones-width sub-derivation-horizontal-gap)))
  (void))

(define (resize-derivation derivation-container)
  (define table (make-mutable-object=-hash))
  (let loop ([derivation-element (send derivation-container get-root)])
    (define derivation-children (send derivation-element get-children))
    (define-values (children-width children-height)
      (for/fold ([width 0] [height 0])
                ([child (in-list derivation-children)])
        (define-values (this-w this-h) (loop child))
        (values (+ width this-w)
                (max height this-h))))
    (define sub-derivation-width
      (if (null? derivation-children)
          0
          (+ children-width (* (- (length derivation-children)
                                  1)
                               sub-derivation-horizontal-gap))))
    (define-values (term-width term-height) (send derivation-element get-term-size))
    (define-values (name-width name-height) (send derivation-element get-name-size))
    (define derivation-width
      (+ (max sub-derivation-width term-width)
         (or name-width 0)))
    (define derivation-height
      (+ children-height
         sub-derivation-vertical-gap
         term-height))
    (dict-set! table derivation-element (cons derivation-width derivation-height))
    (values derivation-width derivation-height))
  table)

(define-custom-hash-types object=-hash #:key? object? object=? object=-hash-code)
