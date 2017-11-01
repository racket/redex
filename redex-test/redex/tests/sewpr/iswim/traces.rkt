#lang racket/base
(require redex "iswim.rkt" "../traces-colors.rkt" "../space-snip.rkt")

;; has-y? : sexp -> boolean
(define (has-y? s)
  (cond
    [(symbol? s) (eq? s 'y)]
    [(pair? s)
     (or (has-y? (cdr s))
         (has-y? (car s)))]
    [else #f]))

(with-colors
 (lambda ()
   (traces/ps iswim-red
              (term ((λ y (y y)) (λ x (x x))))
              "omega.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:layout
              (lambda (tns)
                (for-each
                 (λ (tn)
                   (cond
                     [(has-y? (term-node-expr tn))
                      (term-node-set-position! tn 20 0)]
                     [else
                      (term-node-set-position! tn 20 50)]))
                 tns)))))
