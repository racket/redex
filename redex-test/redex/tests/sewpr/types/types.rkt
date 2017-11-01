#lang scheme

(require redex "../iswim/iswim.rkt")

;; START lang
(define-extended-language t-iswim iswim
  (M X (λ X T M) (M M) b (o2 M M) (o1 M))
  (V b X (λ X T M))
  ((T S) (-> T T) num)
  (Γ ((X T) ...)))
;; STOP lang

;; START tc
;; TC : Γ M -> T or #f
;; type checks a term M in the environment Γ
(define-metafunction t-iswim
  [(TC Γ b)
   (ℬ b)]
  [(TC Γ X)
   (TCvar Γ X)]
  [(TC ((Y S) ...) (λ X T M))
   (TCλ T (TC ((Y S) ... (X T)) M))]
  [(TC Γ (M N))
   (TCapp (TC Γ M) (TC Γ N))]
  [(TC Γ (o M ...))
   (TCo (o (TC Γ M) ...))])
;; STOP tc

;; the #; comment elides this, so there are no
;; duplicate name errors, but this defn still shows
;; up in the tutorial

#;
;; START tcvaralt
;; TCvar : Γ X -> T or #f
(define-metafunction t-iswim
  [(TCvar ((Y S) ... (X T)) X) T]
  [(TCvar ((Y S) ... (X T)) Z) (TCvar ((Y S) ...) Z)]
  [(TCvar () Z) #f])
;; STOP tcvaralt

;; START tcvar
;; TCvar : Γ X -> T or #f
(define-metafunction t-iswim
  [(TCvar ((X T_1) ... (Y T_2) (Z T_3) ...) Y) 
   T_2
   (side-condition (not (member (term Y) (term (Z ...)))))]
  [(TCvar Γ X) #f])
;; STOP tcvar

;; START tclam
;; TCλ : T (or/c T #f) -> T or #f
;; type checks a lambda expression, given the type 
;; of the parameter and the type of the body
(define-metafunction t-iswim
  [(TCλ T S) (-> T S)]
  [(TCλ T #f) #f])
;; STOP tclam

;; START tcapp
;; TCapp : (or/c T #f) (or/c T #f) -> T or #f
(define-metafunction t-iswim
  [(TCapp (-> S T) S) T]
  [(TCapp any_1 any_2) #f])
;; STOP tcapp

;; START tco
;; TCo : o (or/c T #f) ... -> T or #f
(define-metafunction t-iswim
  [(TCo (o T ...)) (∆ (o T ...))]
  [(TCo (o any ...)) #f])
;; STOP tco

;; START delta
;; ∆ : (o T ...) -> T or #f
;; returns the result type for the operator
(define-metafunction t-iswim
  [(∆ (iszero num)) (-> num (-> num num))]
  [(∆ (add1 num)) num]
  [(∆ (sub1 num)) num]
  [(∆ (+ num num)) num]
  [(∆ (- num num)) num]
  [(∆ (* num num)) num]
  [(∆ (/ num num)) num]
  [(∆ (↑ num num)) num]
  [(∆ any) #f])
;; STOP delta

;; START B
;; ℬ : b -> 'num or #f
;; returns the type of literal constants 
(define-metafunction t-iswim
  [(ℬ number) num]
  [(ℬ any) #f])
;; STOP B

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

(define-metafunction t-iswim

  ;; 1. X_1 bound, so don't continue in λ body
  [(t-subst (λ X_1 T any_2) X_1 any_1)
   (λ X_1 T any_2)]
  
  ;; 2. do capture avoiding substitution
  ;;    by generating a fresh name
  [(t-subst (λ X_2 T any_2) X_1 any_1)
   (λ X_new T
     (t-subst (subst-var any_2 X_2 X_new) X_1 any_1))
   (where X_new ,(variable-not-in (term (X_1 any_1 any_2)) 
                                  (term X_2)))]
  ;; 3. replace X_1 with any_1
  [(t-subst X_1 X_1 any_1) any_1]
  
  ;; the last two cases just recur on 
  ;; the tree structure of the term
  [(t-subst (any_2 ...) X_1 any_1)
   ((t-subst any_2 X_1 any_1) ...)]
  [(t-subst any_2 X_1 any_1) any_2])

(provide TC t-iswim t-iswim-red ∆ ℬ t-subst)

(define-term Y
  (λ body-proc
    ((λ fX (fX fX))
     (λ fX ((λ f (body-proc f))
            (λ x ((fX fX) x)))))))

(define example
  (term
   ;; START triexercise
   ((Y (λ tri (λ x
                ((((iszero x)
                   (λ y 0))
                  (λ y (+ x (tri (- x 1)))))
                 0))))
    3)
   ;; STOP triexercise
   ))

(unless (equal? (apply-reduction-relation* iswim-red example) '(6))
  (error 'types.rkt "tri test case failed"))
