#lang racket/base

(require redex/benchmark
         "util.rkt"
         redex/reduction-semantics)
(provide (all-defined-out))

(define the-error "replace all variables")

(define-rewrite bug5
  (subst x x M_x)
  ==> 
  (subst x y M_x)
  #:context (define-metafunction)
  #:once-only)

(include/rewrite (lib "redex/examples/stlc+lists+subst.rkt") stlc-sub bug5)

(include/rewrite "generators.rkt" generators bug-mod-rw)

(define small-counter-example 
  (term ((λ (b int) (λ (a (list int)) (hd a))) 0)))

(test small-counter-example)
