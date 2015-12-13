#lang racket/base

(require scribble/manual
         scribble/racket
         (for-syntax racket/base
                     racket/syntax))

(provide pattern defpattech ttpattern pattech
         tttterm tterm ttpattern-sequence)

(define-syntax (defpattech stx)
   (syntax-case stx ()
     [(_ arg)
      (identifier? #'arg)
      (let ([as (symbol->string (syntax-e #'arg))]
            [pat:arg (format-id #'arg "pat:~a" (syntax-e #'arg))]
            [arg-str (symbol->string (syntax-e #'arg))])
        #`(index '("Redex Pattern" #,as) (deftech #:style? #f #:key #,arg-str (racket #,pat:arg))))]))

(define-syntax (pattech stx)
   (syntax-case stx ()
     [(_ arg)
      (identifier? #'arg)
      (with-syntax ([pat:arg (format-id #'arg "pat:~a" (syntax-e #'arg))])
        #'(racket pat:arg))]))

(define-syntax (ttpattern stx)
   (syntax-case stx ()
    [(_ args ...)
     #'((tech (racketvarfont "pattern")) args ...)]
    [x (identifier? #'x) #'(tech (racketvarfont "pattern"))]))

(define-syntax (ttpattern-sequence stx)
   (syntax-case stx ()
    [(_ args ...)
     #'((tech #:key "pattern" (racketvarfont "pattern-sequence")) args ...)]
    [x (identifier? #'x) #'(tech #:key "pattern" (racketvarfont "pattern-sequence"))]))

(define-syntax (pattern stx)
   (syntax-case stx ()
    [(_ args ...)
     #'((tech "pattern") args ...)]
    [x (identifier? #'x) #'(tech "pattern")]))

(define-syntax (tttterm stx)
   (syntax-case stx ()
    [(_ args ...)
     #'((tech (racketvarfont "term")) args ...)]
    [x (identifier? #'x) #'(tech (racketvarfont "term"))]))

(define-syntax (tterm stx)
   (syntax-case stx ()
    [(_ args ...)
     #'((tech "term") args ...)]
    [x (identifier? #'x) #'(tech "term")]))

(define-syntax (define-pattern-form stx)
   (syntax-case stx ()
     [(_ id)
      (with-syntax ([pat:id (format-id #'id "pat:~a" (syntax-e #'id))]
                    [id-str (symbol->string (syntax-e #'id))])
        #`(begin
            (provide pat:id)
            (define-syntax pat:id (make-element-id-transformer
                                   (lambda (stx)
                                     #'(tech (racketidfont id-str)))))))]))
(define-syntax-rule
  (define-pattern-forms id ...)
   (begin (define-pattern-form id) ...))

(define-pattern-forms
   any _ number natural integer
   real string boolean variable
   variable-except variable-prefix
   variable-not-otherwise-mentioned
   hole name in-hole hide-hole
   side-condition cross)

(provide pat:symbol)
(define-syntax pat:symbol
   (make-element-id-transformer
    (lambda (stx)
      #'(tech (racketvarfont "symbol")))))

(provide pat:pattern-sequence)
(define-syntax pat:pattern-sequence
   (make-element-id-transformer
    (lambda (stx)
      #'(tech (racketvarfont "pattern-sequence")))))

(provide pat:other-literal)
(define-syntax pat:other-literal
  (make-element-id-transformer
   (lambda (stx)
     #'(tech (racketvarfont "other-literal")))))

