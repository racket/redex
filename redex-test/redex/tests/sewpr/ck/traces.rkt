#lang racket/base
(require redex "../traces-colors.rkt" "ck.rkt" "../space-snip.rkt")

(define ex (term (((λ x (- x 1)) 2) mt)))
#|
(require racket/pretty)
(parameterize ([pretty-print-columns 40])
  (pretty-print ex))

(parameterize ([pretty-print-columns 30])
  (pretty-print ex))
|#

(with-colors
 (λ ()
   (parameterize ([initial-char-width 42])
     (traces/ps ck 
                ex
                "mach-bad.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout
                (λ (tns)
                  (let* ([column-space 200]
                         [gap 20]
                         [root (find-root tns)]
                         [midpoint (vertical-line root 3 #:gap gap)])
                    (term-node-set-position! 
                     midpoint
                     (+ (term-node-x midpoint) column-space)
                     (term-node-y midpoint))
                    (vertical-line midpoint 3 #:up? #t #:gap gap)
                    (term-node-set-position! 
                     midpoint
                     (- (term-node-x midpoint) (/ column-space 2))
                     (term-node-y midpoint))))))))
