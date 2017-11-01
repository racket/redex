#lang scheme
(require redex "bool-standard.ss" "bool-any.ss" 
         "../traces-colors.ss"
         "../space-snip.ss")

(define example (term (∨ (∨ true false) (∨ true true))))

(with-colors
 (lambda ()
   (let ([pb 'not-yet-pb])
     (traces/ps bool-any-red
                example
                "bool-any.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout
                (lambda (tns)
                  (for-each 
                   (λ (tn)
                     (let* ([exp (term-node-expr tn)]
                            [center-column-x 200]
                            [y-offset 20]
                            [y-space-factor 80]
                            [center-column
                             (λ (iy)
                               (term-node-set-position! 
                                tn
                                (- center-column-x (/ (term-node-width tn) 2))
                                (+ y-offset
                                   (- (* iy y-space-factor)
                                      (/ (term-node-height tn) 2)))))])
                       (cond
                         [(and (pair? exp)
                               (and (symbol? (list-ref exp 1))
                                    (symbol? (list-ref exp 2))))
                          ;; reduced both the left and right of the original expression
                          (center-column 1)]
                         [(and (pair? exp)
                               (symbol? (list-ref exp 1)))
                          ;; reduced only the left of the original expression
                          (center-column 0)]
                         [(and (pair? exp)
                               (symbol? (list-ref exp 2)))
                          ;; reduced only the right of the original expression
                          (center-column 2)]
                         [(symbol? exp)
                          ;; the result
                          (term-node-set-position!
                           tn
                           (* center-column-x 3/2)
                           (+ y-offset (- (* y-space-factor 1) (/ (term-node-height tn) 2))))]
                         [else
                          ;; the original term
                          (term-node-set-position!
                           tn
                           0
                           (+ y-offset (- (* y-space-factor 1) (/ (term-node-height tn) 2))))])))
                   tns))))))

(with-colors
 (lambda ()
   (parameterize ([initial-char-width 20])
     (traces/ps bool-standard-red
                example
                "bool-standard.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout
                (lambda (tns)
                  (horizontal-line (find-root tns) 2 #:gap 50))))))
