#lang racket/base

(require redex/benchmark
         "util.rkt"
         redex/reduction-semantics)
(provide (all-defined-out))

(define the-error "copy and paste error in the orient → rule")

(define-rewrite bug6
  [(var-not-in-τ x τ)
   (var-not-in-τ x σ)
   ------------------------
   (var-not-in-τ x (τ → σ))]
  ==> 
  [------------------------
   (var-not-in-τ x (τ → σ))]
  #:context (define-judgment-form)
  #:exactly-once)

(include/rewrite (lib "redex/examples/let-poly.rkt") let-poly bug6)

(include/rewrite "generators.rkt" generators bug-mod-rw exn-rw)

(define small-counter-example (term ((λ a (a a)) +)))

(test small-counter-example)
