#lang racket/base

(require redex/benchmark
         "util.rkt"
         redex/reduction-semantics)
(provide (all-defined-out))

(define the-error "mix up types in the function case")

(define-rewrite bug3
  (unify τ_2 (τ_1 → x) Gx)
  ==> 
  (unify τ_1 (τ_2 → x) Gx)
  #:context (define-judgment-form)
  #:once-only)

(include/rewrite (lib "redex/examples/let-poly.rkt") let-poly bug3)

(include/rewrite "generators.rkt" generators bug-mod-rw)

(define small-counter-example (term (1 cons)))
(define enum-small-counter-example (term (let ((a (λ a a))) a)))

(test small-counter-example)
(test enum-small-counter-example)
