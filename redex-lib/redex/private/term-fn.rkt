#lang racket/base

(require (for-template racket/base "defined-checks.rkt"))
(provide make-term-fn
         term-fn?
         term-fn-get-id
         (struct-out term-id)
         
         (struct-out judgment-form)
         
         (struct-out defined-term)
         defined-term-id?
         defined-check
         not-expression-context
         
         make-language-id
         language-id-nts
         language-id-nt-aliases
         language-id-nt-identifiers
         language-id-nt-hole-map
         language-id-nt-hole-at-top
         language-id-nt-neighbors
         pattern-symbols
         
         build-disappeared-uses

         from-smiley-number
         to-smiley-number

         forward-errortrace-prop)

(define-values (struct-type make-term-fn term-fn? term-fn-get term-fn-set!) 
  (make-struct-type 'term-fn #f 1 0))
(define term-fn-get-id (make-struct-field-accessor term-fn-get 0))

(define-struct term-id (id depth prev-id))

(define (transformer-predicate p? stx)
  (and (identifier? stx)
       (cond [(syntax-local-value stx (λ () #f)) => p?]
             [else #f])))

;; mode: (or/c #f (listof (or/c 'I 'O))  -- #f means the judgment form is actually a relation
(define-struct judgment-form (name mode proc mk-proc lang lws rule-names 
                                   gen-clauses mk-gen-clauses term-proc relation?
                                   cache runtime-judgment-form-id
                                   original-contract-expression-id
                                   compiled-input-contract-pat-id
                                   compiled-output-contract-pat-id
                                   transformer)
  #:property prop:procedure (struct-field-index transformer)
  #:transparent)

(define-struct defined-term (value))
(define (defined-term-id? stx)
  (transformer-predicate defined-term? stx))

(define (defined-check id desc #:external [external id])
  (if (equal? (identifier-binding id) 'lexical)
      (datum->syntax id (syntax-e id) external id)
      (quasisyntax/loc external (check-defined-module (λ () #,id) '#,external #,desc))))

(define (not-expression-context stx)
  (when (eq? (syntax-local-context) 'expression)
    (raise-syntax-error #f "not allowed in an expression context" stx)))

(define-values (language-id make-language-id language-id? language-id-get language-id-set)
  (make-struct-type 'language-id #f 7 0 #f '() #f 0))

(define (language-id-getter stx id n)
  (unless (identifier? stx)
    (raise-syntax-error id "expected an identifier defined by define-language" stx))
  (let ([val (syntax-local-value stx (λ () #f))])
    (unless (and (set!-transformer? val)
                 (language-id? (set!-transformer-procedure val)))
      (raise-syntax-error id "expected an identifier defined by define-language" stx))
    (language-id-get (set!-transformer-procedure val) n)))
(define (language-id-nts stx id) (language-id-getter stx id 1))
(define (language-id-nt-aliases stx id) (language-id-getter stx id 2))
(define (language-id-nt-identifiers stx id) (language-id-getter stx id 3))

;; determine if an nt produces pluggable things
(define (language-id-nt-hole-map stx id) (language-id-getter stx id 4))

;; determine if an nt produces a hole without consuming any input
(define (language-id-nt-hole-at-top stx id) (language-id-getter stx id 5))

;; for cycle checking of extended languages
(define (language-id-nt-neighbors stx id) (language-id-getter stx id 6))

(define pattern-symbols '(any number natural integer real string boolean variable
                              variable-not-otherwise-mentioned hole symbol))

(define (build-disappeared-uses nt-identifiers nt id-stx)
  (cond
    [nt-identifiers
     (define table-entries (hash-ref nt-identifiers nt '()))
     (for/list ([table-entry (in-list (if (syntax? table-entries)
                                          (syntax->list table-entries)
                                          table-entries))])
       (define the-srcloc (vector
                           (syntax-source id-stx)
                           (syntax-line id-stx)
                           (syntax-column id-stx)
                           (syntax-position id-stx)
                           ;; shorten the span so it covers only up to the underscore
                           (string-length (symbol->string nt))))
       (define the-id (datum->syntax table-entry
                                     (syntax-e table-entry)
                                     the-srcloc id-stx))
       (syntax-property the-id 'original-for-check-syntax #t))]
    [else '()]))

(define (to-smiley-number n)
  (define candidate
    (let loop ([n n]
               [chars '()])
      (cond
        [(zero? n) (apply string chars)]
        [(odd? n) (loop (/ (- n 1) 2) (cons #\☹ chars))]
        [else (loop (/ n 2) (cons #\☺ chars))])))
  (cond
    [(equal? candidate "") "☺"]
    [else candidate]))

(define (from-smiley-number str)
  (for/fold ([acc 0])
            ([c (in-string str)])
    (+ (case c [(#\☺) 0] [(#\☹) 1])
       (* 2 acc))))

(module+ test
  (require rackunit)
  (check-equal? (to-smiley-number 0) "☺")
  (check-equal? (to-smiley-number 1) "☹")
  (check-equal? (to-smiley-number 2) "☹☺")
  (check-equal? (to-smiley-number 3) "☹☹")
  (check-equal? (to-smiley-number 18) "☹☺☺☹☺")
  
  (for ([x (in-range 1000)])
    (check-equal? x (from-smiley-number (to-smiley-number x))))
  
  (check-equal? (from-smiley-number "☺☺☺☺☺☺☹☺☺☹☺") 18))


(define (forward-errortrace-prop prop stx)
  (if (and (syntax-property prop 'errortrace:annotate)
           (syntax-source prop))
      (syntax-property stx 'errortrace:annotate #t #t)
      stx))
