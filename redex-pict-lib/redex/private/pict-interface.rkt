#lang racket
#|

This file exports functions that have the same interface as the functions
in racket's pict library but, if rhombus is available, actually build
rhombus picts. No other file in redex should depend on the racket
pict library.

|#

(require (for-syntax syntax/parse racket/syntax)
         (only-in pict/convert pict-convertible?)
         (prefix-in p: pict)
         pict/convert)

(define-syntax (define-rhombus stx)
  (syntax-parse stx
    [(_ mod x:id)
     (define len (string-length (symbol->string (syntax-e #'x))))
     (define r:
       (format-id #'x #:source #'x "r:~a" (syntax-e #'x)))
     #`(begin
         ;; just check that the function actually exists
         (when (module-declared/bool? 'mod)
           (void (dynamic-require 'mod 'x)))
         (define-syntax (#,(syntax-property
                            r:
                            'sub-range-binders
                            (vector (syntax-local-introduce r:) 2 len
                                    (syntax-local-introduce #'x) 0 len))
                         stx)
           (syntax-parse stx
             [x:id (syntax/loc stx (thunk))]
             [(_ args (... ...))
              ;; assume we're always using the same #%app
              (syntax/loc stx ((thunk) args (... ...)))]))
         (define (thunk)
           (dynamic-require 'mod 'x)))]
    [(_ mod x:id ...)
     #'(begin (define-rhombus mod x) ...)]))

(define (module-declared/bool? mod)
  (with-handlers ([exn:fail:filesystem:missing-module? (λ (x) #f)])
    (module-declared? mod #t)))

(provide
 pict-convertible?
 (rename-out
  [p:pict-width pict-width]
  [p:pict-height pict-height]
  [p:pict-descent pict-descent]
  [p:draw-pict draw-pict]
  [p:text-style/c text-style/c]
  [p:dc-for-text-size dc-for-text-size]))

(provide pict?)
(define (pict? p)
  (choose
   (p:pict? p)
   (r:is_pict p)))

(define (to-rhm-pict p)
  (choose p (r:from_handle p)))

;; we need this function to make sure that, when we're in rhombus mode
;; we actually work only with rhombus picts, as rhombus pict functions
;; don't implicitly do pict-convertible conversion
(provide pict-convertible->pict)
(define (pict-convertible->pict p)
  (choose
   (pict-convert p)
   (cond
     [(r:is_pict p)
      p]
     [(p:pict? p)
      (to-rhm-pict p)]
     [(pict-convertible? p)
      (to-rhm-pict (pict-convert p))])))

(provide dc
         blank
         text
         filled-rectangle)

(define (dc draw w h [a h] [d 0])
  (to-rhm-pict (p:dc draw w h a d)))

(define blank
  (case-lambda
    [() (to-rhm-pict (p:blank))]
    [(s) (to-rhm-pict (p:blank s))]
    [(w h) (to-rhm-pict (p:blank w h))]
    [(w a h) (to-rhm-pict (p:blank w a h))]
    [(w h a d) (to-rhm-pict (p:blank w h a d))]))

(define (text content [style '()] [size 12] [angle 0])
  (to-rhm-pict (p:text content style size angle)))

(define (filled-rectangle w h
                          #:draw-border? [draw-border? #t]
                          #:color [color #f]
                          #:border-color [border-color #f]
                          #:border-width [border-width #f])
  (to-rhm-pict
   (p:filled-rectangle w h
                       #:draw-border? draw-border? #:color color
                       #:border-color border-color #:border-width border-width)))

(define-rhombus
  (lib "pict/main.rhm")
  beside
  stack
  overlay)

(define-rhombus
  rhombus/dot
  dynamic-dot-ref)

(define-syntax (choose stx)
  (syntax-parse stx
    [(_ racket-pict:expr rhombus-pict:expr)
     #'(choose/proc (λ () racket-pict)
                    (λ () rhombus-pict))]))
(define (rhombus-present?)
  (module-declared/bool? '(lib "pict/main.rhm")))
(define (choose/proc racket-pict rhombus-pict)
  (cond
    [(rhombus-present?)
     (rhombus-pict)]
    [else
     (racket-pict)]))

(provide horizontal-line)
(define (horizontal-line w)
  (to-rhm-pict
   (p:frame (p:blank w 0))))

(define-syntax-rule
  (define-simple name p:name r:name args ...)
  (define (name args ...)
    (choose
     (p:name args ...)
     (r:name args ...))))

(define-syntax (define-simple-dot stx)
  (syntax-parse stx
    [(_ name p-name:id pict args ...)
     #`(begin
         (provide name)
         (define (name pict args ...)
           (choose
            (p-name pict args ...)
            ((r:dynamic-dot-ref pict 'name) args ...))))]))

(define-simple-dot ghost p:ghost p)
(define-simple-dot launder p:launder p)
(define-simple-dot refocus p:refocus p sub)
(define-simple-dot colorize p:colorize p color)

(provide inset)
(define inset
  (case-lambda
    [(p amt) (choose (p:inset p amt) ((r:dynamic-dot-ref p 'pad) amt))]
    [(p horiz vert)
     (choose (p:inset p horiz vert)
             ((r:dynamic-dot-ref p 'pad) #:horiz horiz #:vert vert))]
    [(p l t r b)
     (choose (p:inset p l t r b)
             ((r:dynamic-dot-ref p 'pad) #:left l #:top t #:right r #:bottom b))]))

(define-syntax (define-append stx)
  (syntax-parse stx
    [(_ name racket-name rhombus-name rhombus-kwd rhombus-kwd-value)
     #'(begin
         (provide name)
         (define (name . in-args)
           (choose
            (apply racket-name in-args)
            (call-rhombus-append rhombus-name 'rhombus-kwd rhombus-kwd-value in-args))))]))

(define (call-rhombus-append rhombus-fn rhombus-kwd rhombus-kwd-value in-args)
  (define-values (sep args)
    (cond
      [(and (pair? in-args) (number? (car in-args)))
       (values (car in-args) (cdr in-args))]
      [else
       (values 0 in-args)]))
  (keyword-apply rhombus-fn
                 (if (keyword<? rhombus-kwd '#:sep)
                     (list rhombus-kwd '#:sep)
                     (list '#:sep rhombus-kwd))
                 (if (keyword<? rhombus-kwd '#:sep)
                     (list rhombus-kwd-value sep)
                     (list sep rhombus-kwd-value))
                 args))

(define-append ht-append
  p:ht-append
  r:beside #:vert 'top)
(define-append htl-append
  p:htl-append
  r:beside #:vert 'topline)
(define-append hc-append
  p:hc-append
  r:beside #:vert 'center)
(define-append hbl-append
  p:hbl-append
  r:beside #:vert 'baseline)
(define-append hb-append
  p:hb-append
  r:beside #:vert 'bottom)
(define-append vc-append
  p:vc-append
  r:stack #:horiz 'center)
(define-append vl-append
  p:vl-append
  r:stack #:horiz 'left)
(define-append vr-append
  p:vl-append
  r:stack #:horiz 'right)

(define-syntax (define-superimpose stx)
  (syntax-parse stx
    [(_ name racket-name horiz vert)
     #'(begin
         (provide name)
         (define (name . args)
           (choose
            (apply racket-name args)
            (apply r:overlay #:horiz horiz #:vert vert args))))]))

(define-superimpose lt-superimpose p:lt-superimpose 'left 'top)
(define-superimpose ltl-superimpose p:ltl-superimpose 'left 'topline)
(define-superimpose lc-superimpose p:lc-superimpose 'left 'center)
(define-superimpose lbl-superimpose p:lbl-superimpose 'left 'baseline)
(define-superimpose lb-superimpose p:lb-superimpose 'left 'bottom)

(define-superimpose ct-superimpose p:ct-superimpose 'center 'top)
(define-superimpose ctl-superimpose p:ctl-superimpose 'center 'topline)
(define-superimpose cc-superimpose p:cc-superimpose 'center 'center)
(define-superimpose cbl-superimpose p:cbl-superimpose 'center 'baseline)
(define-superimpose cb-superimpose p:cb-superimpose 'center 'bottom)

(define-superimpose rt-superimpose p:rt-superimpose 'right 'top)
(define-superimpose rtl-superimpose p:rtl-superimpose 'right 'topline)
(define-superimpose rc-superimpose p:rc-superimpose 'right 'center)
(define-superimpose rbl-superimpose p:rbl-superimpose 'right 'baseline)
(define-superimpose rb-superimpose p:rb-superimpose 'right 'bottom)

(define-namespace-anchor ns-anchor)
(define ns (namespace-anchor->namespace ns-anchor))
(define-values (r:find r:from_handle r:is_pict)
  (cond
    [(rhombus-present?)
     (define rhombus-dynamic-require
       (dynamic-require 'rhombus/dynamic-require 'rhombus-dynamic-require))
     (define rhombus-dynamic-require-predicate
       (dynamic-require 'rhombus/dynamic-require 'rhombus-dynamic-require-predicate))
     (define dynamic-dot-ref
       (dynamic-require 'rhombus/dot 'dynamic-dot-ref))
     (define r:from_handle
       (rhombus-dynamic-require '(lib "pict/main.rhm") '(Pict from_handle)))
     (define r:Find (rhombus-dynamic-require '(lib "pict/main.rhm") '(Find)))
     (define (Find pict sub h v)
       ((dynamic-dot-ref (r:Find sub #:horiz h #:vert v)
                         'in)
        pict))
     (define r:is_pict
       (rhombus-dynamic-require-predicate '(lib "rhombus/pict.rhm") 'Pict))
     (values Find
             r:from_handle
             r:is_pict)]
    [else
     (values "dummy value that's not rhombus's find"
             "dummy value that's not rhombus's find_handle"
             "dummy value that's not rhombus's is_a Pict")]))
(define-syntax (define-finder stx)
  (syntax-parse stx
    [(_ name racket-name horiz vert)
     #`(begin
         (provide name)
         (define (name pict subpict)
           (finder-check subpict)
           (choose
            (racket-name pict subpict)
            (r:find pict subpict horiz vert)))
         (hash-set! finder-table
                    name
                    (cons horiz vert)))]))
(define (finder-check subpict)
  (unless (pict? subpict)
    (error 'name "the version in pict-interface.rkt supports only picts, not pict paths\n  ~s" subpict)))
(define finder-table (make-hash))

(define-finder lt-find p:lt-find 'left 'top)
(define-finder ltl-find p:lt-find 'left 'topline)
(define-finder lc-find p:lt-find 'left 'center)
(define-finder lbl-find p:lt-find 'left 'baseline)
(define-finder lb-find p:lt-find 'left 'bottom)

(define-finder ct-find p:lt-find 'center 'top)
(define-finder ctl-find p:lt-find 'center 'topline)
(define-finder cc-find p:lt-find 'center 'center)
(define-finder cbl-find p:lt-find 'center 'baseline)
(define-finder cb-find p:lt-find 'center 'bottom)

(define-finder rt-find p:lt-find 'right 'top)
(define-finder rtl-find p:lt-find 'right 'topline)
(define-finder rc-find p:lt-find 'right 'center)
(define-finder rbl-find p:lt-find 'right 'baseline)
(define-finder rb-find p:lt-find 'right 'bottom)

(provide pin-over)
(define (pin-over base dx dy pict)
  (choose
   (p:pin-over base dx dy pict)
   (cond
     [(real? dx)
      (r:overlay base #:dx dx #:dy dy pict)]
     [else
      (define hv (hash-ref finder-table dy))
      (define-values (dx dy) (r:find base dx (car hv) (cdr hv)))
      (r:overlay base #:dx dx #:dy dy pict)])))

(provide add-redex-property)
(define (add-redex-property p what)
  (choose
   p
   (cond
     [what
      (define rhm-p (pict-convertible->pict p))
      ((r:dynamic-dot-ref rhm-p
                          'set_metadata)
       (hash-set ((r:dynamic-dot-ref rhm-p 'metadata)) "redex" what))]
     [else p])))
