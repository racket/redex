#lang racket/base
(require "1.rkt" 
         "types.rkt"
         "../traces-colors.rkt"
         "../space-snip.rkt"
         redex)

(define (bw-ize f)
  (lambda (x) 
    (cond
      [(not (f x)) "gray"]
      [else #t])))

(with-colors
 (λ ()
   (traces/ps mod3 
              (term (+ (+ 1 1) (+ 2 1))) 
              "1.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:layout 
              (lambda (tns)
                (let* ([root (find-root tns)]
                       [root-children (term-node-children root)])
                  (let-values ([(leaf-child continue-child)
                                (if (null? (term-node-children (car root-children)))
                                    (values (car root-children)
                                            (cadr root-children))
                                    (values (cadr root-children)
                                            (car root-children)))])
                    (let ([last (car (term-node-children continue-child))])
                      (center-below root continue-child)
                      (center-right root leaf-child)
                      (center-right continue-child last)
                      (term-node-set-position! last 
                                               (term-node-x leaf-child)
                                               (term-node-y last))))))
              #:pred
              (bw-ize (redex-match mod-lang A)))
   
   (traces/ps t-iswim-red
              (term (+ ((λ x num x) 1) 2))
              "tc-ok.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:pred
              (bw-ize (λ (x) (term (TC () ,x))))
              #:layout
              (lambda (tns)
                (horizontal-line (find-root tns) 2)))
   
   (traces/ps t-iswim-red
              (term (((λ x num (λ y num x)) 2) 3))
              "tc-bad.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:pred
              (bw-ize (λ (x) (term (TC () ,x))))
              #:layout
              (lambda (tns)
                (horizontal-line (find-root tns) 1)))))
