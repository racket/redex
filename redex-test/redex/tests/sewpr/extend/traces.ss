#lang scheme
(require redex "eiswim.ss" "../traces-colors.ss" "../space-snip.ss")
(define err0
  (term (/ ((λ x (/ 1 x)) 7) 2)))

(define err1
  (term (/ ((λ x (+ (/ 1 x) (err 2))) 7) 2)))

(define ((layout hspace) tns)
  (let* ([root (find-root tns)]
         [one (car (term-node-children root))]
         [two (car (term-node-children one))]
         [three (car (term-node-children two))])
    (vertical-line root 1)
    (term-node-set-position! 
     two 
     (+ (term-node-width root) (term-node-x root) hspace)
     (+ (term-node-y root)
        (/ (term-node-height root) 2)
        (/ (term-node-height two) -2)))
    (term-node-set-position! 
     three 
     (+ (term-node-x two)
        (/ (term-node-width two) 2)
        (/ (term-node-width three) -2))
     (+ (term-node-y one)
        (/ (term-node-height one) 2)
        (/ (term-node-height three) -2)))))

(with-colors
 (λ ()
   (traces/ps e-iswim-red-first-try
              err0
              "err0.ps"
              #:post-process rewrite-pb
              #:edge-label-font edge-label-font
              #:layout (layout 20))))

(with-colors
 (λ ()
   (parameterize ([initial-char-width 24])
     (traces/ps e-iswim-red-first-try
                err1
                "err1.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout (layout 10)))))

(with-colors
 (λ ()
   (parameterize ([initial-char-width 24])
     (traces/ps e-iswim-red
                err1
                "err.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout (layout 10)))))
