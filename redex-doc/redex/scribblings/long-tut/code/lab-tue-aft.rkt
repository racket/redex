#lang racket

(require redex "common.rkt" "tc-common.rkt")

;; =============================================================================
;; LAB
;; =============================================================================

(define-extended-language TLambda-bool-tc TLambda-tc
  (e ::= .... tt ff s-and)
  (t ::= .... bool))

(define e4 (term (lambda ((x bool)) (s-and x tt))))

(module+ test
  (test-equal (redex-match? TLambda-bool-tc e e4) #true))

(module+ test
  (test-equal (judgment-holds (⊢b () tt bool)) #true)
  (test-equal (judgment-holds (⊢b ((x bool)) x bool)) #true)
  (test-equal (judgment-holds (⊢b () s-and t) t) (term [(bool bool -> bool)]))
  (test-equal (judgment-holds (⊢b () s-and (bool bool -> bool))) #true)
  (test-equal (judgment-holds (⊢b () (s-and tt tt) t) t) (term [bool]))
  (test-equal (judgment-holds (⊢b () ,e4 t) t) (term [(bool -> bool)])))

(define-judgment-form TLambda-bool-tc
  #:mode (⊢b I I O)
  #:contract (⊢b Γ e t)

  [----------------------- "number"
   (⊢b Γ n int)]

  [----------------------- "+"
   (⊢b Γ + (int int -> int))]
  
  [----------------------- "variable"
   (⊢b Γ x (lookup Γ x))]

  [(⊢b (extend Γ (x_1 t_1) ...) e t)
   ------------------------------------------------- "lambda"
   (⊢b Γ (lambda ((x_1 t_1) ...) e) (t_1 ... -> t))]

  [(⊢b Γ e_1 (t_2 ..._n -> t))
   (⊢b Γ e_2 t_2) ...
   ------------------------------------------------- "application"
   (⊢b Γ (e_1 e_2 ..._n) t)]

  [--------------- "tt"
   (⊢b Γ tt bool)]

  [--------------- "ff"
   (⊢b Γ ff bool)]

  [
   ---------------------------------- "s-and"
   (⊢b Γ s-and (bool bool -> bool))])

;; -----------------------------------------------------------------------------
(module+ test
  (test-results))
