#lang racket/base
(require redex/reduction-semantics "../iswim/iswim.rkt")

;; as before: 
;; ∆ : (o T ...) -> T
;; ℬ : b -> (term num) 
;; t-subst
(require (only-in "types.rkt" ∆ ℬ t-subst))

;; START lang
(define-extended-language t-iswim iswim
  (M X (λ X T M) (M M) b (o2 M M) (o1 M))
  (V b X (λ X T M))
  ((T S) (-> T T) num)
  (Γ ((X T) ...)))
;; STOP lang

;; START tc
;; TC : Γ M -> T 
;; \underline{exception: exn:fail:redex if no type exists}
;; type checks a term M in the environment Γ
(define-metafunction t-iswim
  [(TC Γ b) (ℬ b)]
  [(TC Γ X) (TCvar Γ X)]
  [(TC ((Y S) ...) (λ X T M)) 
   (-> T (TC ((Y S) ... (X T)) M))]
  [(TC Γ (M N)) (TCapp (TC Γ M) (TC Γ N))]
  [(TC Γ (o M ...)) (∆ (o (TC Γ M) ...))])

;; TCvar : Γ X -> T
(define-metafunction t-iswim
  [(TCvar ((Y T_1) ... (X T_2) (Z T_3) ...) X) 
   T_2
   (side-condition (not (member (term X) (term (Z ...)))))])

;; TCapp : T T -> T
(define-metafunction t-iswim
  [(TCapp (-> S T) S) T])
;; STOP tc

;; START red
(define t-iswim-red
  (reduction-relation
   t-iswim
   (--> (in-hole E ((λ X T M) V))
        (in-hole E (t-subst V X M))
        βv)
   (--> (in-hole E (o b ...))
        (in-hole E (δ (o b ...)))
        δ)))
;; STOP red

(provide TC t-iswim t-iswim-red)
