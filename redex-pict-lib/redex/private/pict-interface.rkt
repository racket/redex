#lang racket
(require (for-syntax syntax/parse racket/syntax)
         (only-in pict/convert pict-convertible?)
         (prefix-in p: pict)
         pict)

(define-syntax (define-rhombus stx)
  (syntax-parse stx
    [(_ mod x:id)
     (define len (string-length (symbol->string (syntax-e #'x))))
     (define r:
       (format-id #'x #:source #'x "r:~a" (syntax-e #'x)))
     #`(begin
         ;; just check that the function actually exists
         (when (module-declared? 'mod #t)
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


(provide
 pict-convertible?
 (rename-out
  [p:pict-width pict-width]
  [p:pict-height pict-height]
  [p:pict? pict?]
  [p:draw-pict draw-pict]
  [p:dc dc]
  [p:text-style/c text-style/c]
  [p:blank blank]
  [p:pict-descent pict-descent]
  [p:text text]
  [p:dc-for-text-size dc-for-text-size]
  [p:filled-rectangle filled-rectangle]))

(define-rhombus
  (lib "pict/main.rhm")
  rectangle ;; just temporary
  beside
  stack
  overlay
  line)

(define-rhombus
  rhombus/dot
  dynamic-dot-ref)

(define-syntax (choose stx)
  (syntax-parse stx
    [(_ racket-pict:expr rhombus-pict:expr)
     #'(choose/proc (λ () racket-pict)
                    (λ () rhombus-pict))]))
(define (rhombus-present?)
  (module-declared? '(lib "pict/main.rhm") #t))
(define (choose/proc racket-pict rhombus-pict)
  (cond
    [(rhombus-present?)
     (rhombus-pict)]
    [else
     (racket-pict)]))

(provide horizontal-line)
(define (horizontal-line w)
  (choose
   (p:frame (p:blank w 0))
   (r:line #:dx w)))

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
    [(p amt) (choose (p:inset amt) ((r:dynamic-dot-ref p 'pad) amt))]
    [(p horiz vert)
     (choose (p:inset horiz vert)
             ((r:dynamic-dot-ref p 'pad) #:horiz horiz #:vert vert))]
    [(p l t r b)
     (choose (p:inset l t r b)
             ((r:dynamic-dot-ref p 'pad) #:left l #:top t #:right r #:bottom b))]))

(define-syntax (define-append stx)
  (syntax-parse stx
    [(_ name racket-name rhombus-name rhombus-kwd rhombus-kwd-value)
     #'(begin
         (provide name)
         (define (name arg1 . args)
           (printf ">> ~s ~s ~s\n" name rhombus-name (cons arg1 args))
           (choose
            (apply racket-name arg1 args)
            (keyword-apply rhombus-name
                           (if (keyword<? 'rhombus-kwd '#:sep)
                               (list 'rhombus-kwd '#:sep)
                               (list '#:sep 'rhombus-kwd))
                           (if (keyword<? 'rhombus-kwd '#:sep)
                               (list rhombus-kwd-value (if (number? arg1) arg1 0))
                               (list (if (number? arg1) arg1 0) rhombus-kwd-value))
                           (if (number? arg1)
                               args
                               (let ([ans (cons arg1 args)])
                                 (printf "?? ~s\n" ans)
                                 ans))))))]))

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
           (printf "calling ~s with ~s\n" name args)
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
(define r:find
  (cond
    [(rhombus-present?)
     (parameterize ([current-namespace ns])
       (namespace-require '(all-except rhombus #%top))
       (namespace-require 'rhombus/parse)
       (namespace-require 'redex/private/rhombus-bridge)
       ;(eval `(rhombus-top (group def π (op =) 3.14)))
       ;(eval 'π)
       (eval 'find))]
    [else
     #f]))
(define-syntax (define-finder stx)
  (syntax-parse stx
    [(_ name racket-name horiz vert)
     #`(begin
         (provide name)
         (define (name pict subpict)
           (unless (pict? subpict)
             (error 'name "the version in pict-interface.rkt supports only picts, not pict paths"))
           (choose
            (racket-name pict subpict)
            (r:find pict subpict horiz vert)))
         (hash-set! finder-table
                    name
                    (cons horiz vert)))]))
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
