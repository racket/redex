#lang racket/base
(require redex
         "../traces-colors.rkt"
         "../space-snip.rkt"
         "cont.rkt")

(define ex (term (+ 1 (call/cc (λ k (+ (λ y y) (k 12)))))))

(with-colors
 (λ ()
   (parameterize ([initial-char-width 20])
     (traces/ps c-iswim-red
                ex
                "cont-basic.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout
                (λ (tns)
                  (let* ([root (find-root tns)]
                         [_ (term-node-set-position!
                             root 
                             (term-node-x root)
                             (+ (term-node-y root) 200))]
                         [t1 (horizontal-line root 1 #:gap 80)]
                         [t2 (vertical-line t1 1)]
                         [t3 (horizontal-line t2 1 #:left? #t)]
                         [t4 (vertical-line t3 1 #:up? #t)]
                         [t5 (horizontal-line t4 1)])
                    (void)))))
   
   (parameterize ([initial-char-width 22])
     (traces/ps ☺-iswim-red
                ex
                "cont-smile.ps"
                #:post-process rewrite-pb
                #:edge-label-font edge-label-font
                #:layout
                (λ (tns)
                  (let* ([root (find-root tns)]
                         [_ (term-node-set-position!
                             root 
                             (term-node-x root)
                             (+ (term-node-y root) 200))]
                         [t1 (horizontal-line root 1 #:gap 80)]
                         [t2 (vertical-line t1 1 #:gap 25)]
                         [t3 (horizontal-line t2 1 #:left? #t #:gap 80)]
                         [t4 (vertical-line t3 1 #:up? #t #:gap 30)])
                    (void)))))))

