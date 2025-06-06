#lang racket/base
(require racket/promise (for-syntax racket/base))
(provide (struct-out nt) make-multi-name-nt
         (struct-out rhs)
         (struct-out bind)
         (struct-out mismatch-bind)
         (struct-out compiled-pattern)
         mtch
         mtch?
         make-mtch
         mtch-bindings
         mtch-context
         mtch-hole
         bindings?
         make-bindings
         bindings-table
         empty-bindings
         the-not-hole
         the-hole
         hole?
         term/pretty-write-doing-the-printing
         (struct-out compiled-lang) 
         compiled-lang-across-ht 
         compiled-lang-across-list-ht
         compiled-lang-cclang
         default-language

         extend-nt-ellipses
         (for-syntax extend-nt-ellipses)
         (struct-out derivation)
         include-entire-derivation
         include-jf-rulename)

(begin-for-syntax
  (define extend-nt-ellipses '(....)))
(define extend-nt-ellipses '(....))

;; lang = (listof nt)
;; nt = (make-nt sym (listof rhs))
;; rhs = (make-rhs single-pattern)
;; single-pattern = sexp
(define-struct nt (name rhs) #:transparent)
(define-struct rhs (pattern) #:transparent)
(define term/pretty-write-doing-the-printing (make-parameter #f))
(define-values (the-hole the-not-hole hole?)
  (let ()
    (struct hole (which)
      #:property prop:equal+hash (list (λ (x y recur) #t)
                                       (λ (v recur) 255)
                                       (λ (v recur) 65535))
      #:methods gen:custom-write
      [(define (write-proc a-hole port mode)
         (define str (if (equal? (hole-which a-hole) 'the-hole)
                         "hole"
                         "not-hole"))
         (cond
           [(or (equal? mode 0) (equal? mode 1) (term/pretty-write-doing-the-printing))
            (write-string str port)]
           [else
            (write-string "#<" port)
            (write-string str port)
            (write-string ">" port)]))]
      #:inspector #f)
    (define the-hole (hole 'the-hole))
    (define the-not-hole (hole 'the-not-hole))
    (values the-hole the-not-hole hole?)))

(define (make-multi-name-nt names rhs)
  (make-nt (sort names symbol<?) rhs))

;; bindings = (make-bindings (listof rib))
;; rib = (make-bind sym sexp)
;; if a rib has a pair, the first element of the pair should be treated as a prefix on the identifier
;; NOTE: the bindings may contain mismatch-ribs temporarily, but they are all removed
;;       by merge-multiples/remove, a helper function called from match-pattern
(define-values (bindings make-bindings bindings-table bindings? empty-bindings)
  (let ()
    (define-struct bindings (table) #:transparent) ;; for testing, add inspector
    (define empty-bindings (make-bindings '()))
    (values bindings
            (lambda (table) (if (null? table) empty-bindings (make-bindings table)))
            bindings-table
            bindings?
            empty-bindings)))


;; compiled-pattern : exp hole-info nesting-depth -> (union #f (listof mtch))
;; mtch = (make-mtch bindings sexp[context] (union none sexp[hole]))
;; hole-info = boolean
;;               #f means we're not in a `in-hole' context
;;               #t means we're looking for a hole
(define-values (mtch mtch-bindings mtch-context mtch-hole make-mtch mtch?)
  (let ()
    (define-struct mtch (bindings context hole) #:inspector (make-inspector))
    (values mtch
            mtch-bindings
            mtch-context
            mtch-hole
            (lambda (a b c)
              (unless (bindings? a)
                (error 'make-mtch "expected bindings for first agument, got ~e" a))
              (make-mtch a b c))
            mtch?)))

(define-struct bind (name exp) #:transparent)
(define-struct mismatch-bind (name exp nesting-depth) #:transparent)


;; compiled-lang : 
;;   (make-compiled-lang (listof nt) 
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> boolean]
;;                       hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                       hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                       hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                       pict-builder
;;                       (listof symbol)
;;                       hash[sym -o> pattern]
;;                       (listof (list compiled-pattern bspec))
;;                       (hash/c symbol? enum?)) ;; see enum.rkt

(define-struct compiled-lang (lang delayed-cclang ht list-ht all-ht raw-across-ht raw-across-list-ht
                                   has-hole-or-hide-hole-ht cache binding-forms-absent-cache
                                   bind-names-cache pict-builder
                                   literals aliases collapsible-nts
                                   ambiguity-cache binding-table enum-table
                                   language-name)
   #:methods gen:custom-write
  [(define (write-proc clang port mode)
     (define lang-name (compiled-lang-language-name clang))
     (display "#<language: " port)
     (display lang-name port)
     (display ">" port))])

(define (compiled-lang-cclang x) (force (compiled-lang-delayed-cclang x)))
(define (compiled-lang-across-ht x)
  (compiled-lang-cclang x) ;; ensure this is computed
  (compiled-lang-raw-across-ht x))
(define (compiled-lang-across-list-ht x) 
  (compiled-lang-cclang x) ;; ensure this is computed
  (compiled-lang-raw-across-list-ht x))

(define default-language (make-parameter #f))

(define-struct compiled-pattern (cp binds-names? skip-dup-check? lang-α-equal?) #:transparent)

(struct derivation (term name subs) 
  #:extra-constructor-name make-derivation
  #:transparent
  #:guard (λ (term name subs struct-name)
            (unless (or (not name) (string? name))
              (raise-argument-error struct-name "(or/c string? #f)" 1 term name subs))
            (unless (and (list? subs)
                         (andmap derivation? subs))
              (raise-argument-error struct-name "derivation?" 2 term name subs))
            (values term name subs)))


;; judgment-form parameters
(define include-entire-derivation (make-parameter #f))
(define include-jf-rulename (make-parameter #f))
