#lang racket/base
(require racket/promise)
(provide (struct-out nt)
         (struct-out rhs)
         the-not-hole
         the-hole
         hole?
         (struct-out compiled-lang) 
         compiled-lang-across-ht 
         compiled-lang-across-list-ht
         compiled-lang-cclang)

;; lang = (listof nt)
;; nt = (make-nt sym (listof rhs))
;; rhs = (make-rhs single-pattern)
;; single-pattern = sexp
(define-struct nt (name rhs) #:transparent)
(define-struct rhs (pattern) #:transparent)
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
           [(or (equal? mode 0) (equal? mode 1))
            (write-string str port)]
           [else
            (write-string "#<" port)
            (write-string str port)
            (write-string ">" port)]))]
      #:inspector #f)
    (define the-hole (hole 'the-hole))
    (define the-not-hole (hole 'the-not-hole))
    (values the-hole the-not-hole hole?)))



;; compiled-lang : 
;;   (make-compiled-lang (listof nt) 
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> compiled-pattern]
;;                       hash[sym -o> boolean])
;;                       hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                       hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                       pict-builder
;;                       (listof symbol)
;;                       (listof (listof symbol)) -- keeps track of `primary' non-terminals
;;                       hash[sym -o> pattern]
;;                       (hash/c symbol? enum?)) ;; see enum.rkt

(define-struct compiled-lang (lang delayed-cclang ht list-ht raw-across-ht raw-across-list-ht
                                   has-hole-or-hide-hole-ht cache bind-names-cache pict-builder
                                   literals nt-map collapsible-nts
                                   ambiguity-cache enum-table))

(define (compiled-lang-cclang x) (force (compiled-lang-delayed-cclang x)))
(define (compiled-lang-across-ht x)
  (compiled-lang-cclang x) ;; ensure this is computed
  (compiled-lang-raw-across-ht x))
(define (compiled-lang-across-list-ht x) 
  (compiled-lang-cclang x) ;; ensure this is computed
  (compiled-lang-raw-across-list-ht x))
