#lang racket/base

(require redex/benchmark
         "util.rkt"
         redex/reduction-semantics)
(provide (all-defined-out))

(define the-error
  (string-append "dropped the occurs check"))

(define-rewrite bug4
  [(var-not-in-τ x τ)
   (uh (eliminate-G x τ G) Gx)
   (where Gx_eliminated (eliminate-Gx x τ Gx))
   (where τ_subst (apply-subst-τ Gx τ))
   ---------------------------------------------------- "variable elim"
   (uh (x τ G)
       (x τ_subst Gx_eliminated))]
  ==> 
  [(uh (eliminate-G x τ G) Gx)
   (where Gx_eliminated (eliminate-Gx x τ Gx))
   (where τ_subst (apply-subst-τ Gx τ))
   ---------------------------------------------------- "variable elim"
   (uh (x τ G)
       (x τ_subst Gx_eliminated))]
  #:context (define-judgment-form)
  #:once-only)

(include/rewrite (lib "redex/examples/let-poly.rkt") let-poly bug4)

(include/rewrite "generators.rkt" generators bug-mod-rw exn-rw)

(define small-counter-example (term ((λ a (a a)) hd)))

(test small-counter-example)
