#lang racket
(require redex)

(provide (all-defined-out))

;; This semantics comes from the paper
;; _A Natural Semantics for Lazy Evaluation_,
;; by John Launchbury, POPL 1993
;; extended with integers, +, and if0.

(define-language L
  (e ::=
     v
     (e x)
     (let ([x e] ...) e)
     x
     (+ e e)        ;; add addition
     (if0 e e e))   ;; add conditional
  (v ::=            ;; don't use 'z' for values,
     ;;                because that's confusing
     i              ;; add integer constants
     (λ (x) e))

  (i ::= integer)
  (x y z ::= variable-not-otherwise-mentioned)

  (Γ Δ Θ ::= · (Γ x ↦ e))

  #:binding-forms
  (let ([x e] ...) e_body #:refers-to (shadow x ...))
  (λ (x) e #:refers-to x))

(define-judgment-form L
  #:mode (⇓ I I O O)
  #:contract (⇓ Γ e Δ v)


  [----------- Value
   (⇓ Γ v Γ v)]


  [(⇓ Γ e Δ (λ (y) e_*))
   (⇓ Δ (substitute e_* y x) Θ v)
   ------------------------- Application
   (⇓ Γ (e x) Θ v)]


  [(where (Γ x ↦ e) (separate Γ_* x))
   (⇓ Γ e Δ v)
   (where Δ_* (Δ x ↦ v))
   ---------------------------------- Variable
   (⇓ Γ_* x Δ_* v)]


  [(⇓ (extend Γ (x_i e_i) ...) e Δ v)
   ---------------------------------- Let
   (⇓ Γ (let ([x_i e_i] ...) e) Δ v)]


  [(⇓ Γ e_1 Θ i_1)
   (⇓ Θ e_2 Δ i_2)
   ---------------------------------------------- Add
   (⇓ Γ (+ e_1 e_2) Δ ,(+ (term i_1) (term i_2)))]


  [(⇓ Γ e_1 Θ i)
   (⇓ Θ (choose i e_2 e_3) Δ v)
   ---------------------------- If
   (⇓ Γ (if0 e_1 e_2 e_3) Δ v)])

(define-metafunction L
  choose : i e e -> e
  [(choose 0 e_1 e_2) e_1]
  [(choose i e_1 e_2) e_2])

(define-metafunction L
  separate : Γ x -> (Γ x ↦ e) or ⊥
  [(separate · x) ⊥]
  [(separate (Γ x ↦ e) x) (Γ x ↦ e)]
  [(separate (Γ y ↦ e_*) x)
   ((Γ_* y ↦ e_*) x ↦ e)
   (where (Γ_* x ↦ e) (separate Γ x))]
  [(separate (Γ y ↦ e_*) x) ⊥
   (where ⊥ (separate Γ x))])

(define-metafunction L
  extend : Γ (x e) ... -> Γ
  [(extend Γ) Γ]
  [(extend Γ (x e) (x_* e_*) ...)
   (extend (Γ x ↦ e) (x_* e_*) ...)])



(define e? (redex-match? L e))
(define v? (redex-match? L v))
(define T-v? (redex-match? L (T v)))


;; run a program to get it's result
(define/contract (run p)
  (-> e? (or/c v? #f))
  (define vs (judgment-holds (⇓ · ,p Δ v) v))
  (cond
    [(pair? vs)
     (unless (= 1 (length vs))
       (error 'run "multiple results ~s" vs))
     (car vs)]
    [else #f]))

;; opens a visualization of the derivation
(define (show p)
  (-> e? void?)
  (show-derivations
   (build-derivations
    (⇓ · ,p Δ v))))

(module+ test

  (default-language L)

  ;; replace-free, rename-bound, and subst tests omitted, since those metafunctions are gone

  (test-equal (term (separate · x)) (term ⊥))
  (test-equal (term (separate (· x ↦ 1) x)) (term (· x ↦ 1)))
  (test-equal (term (separate ((· x ↦ 1) y ↦ 2) x))
                (term ((· y ↦ 2) x ↦ 1)))
  (test-equal (term (separate (· x ↦ 1) y)) (term ⊥))

  ;; ^ tests omitted, since that metafunction is gone

  (test-equal (judgment-holds (⇓ (· y ↦ 1) ((λ (x) x) y) Δ v) v)
                (list (term 1)))

  (test-equal (run (term 1)) 1)
  (test-equal (run (term (let ([y 1])
                             (let ([z ((λ (x) x) y)])
                               2))))
                2)
  (test-equal (run (term (let ([y 1]) y))) 1)
  (test-equal (run (term (let ([y (λ (x) x)]) y))) (term (λ (x1) x1)))
  (test-equal (run (term (let ([y 1]) ((λ (x) x) y)))) 1)
  (test-equal (run (term
                      (let ([app (λ (f) (λ (x) (f x)))]
                            [f (λ (x) (λ (y) x))]
                            [o 1])
                        (((app f) o) f))))
                1)
  (test-equal (run (term (if0 0 1 2))) 1)
  (test-equal (run (term (if0 1 2 3))) 3)

  ;; free variable errors return no derivation
  (test-equal (run (term (let ([x y]) x))) #f)

  ;; as do runtime errors
  (test-equal (run (term (let ([two 2]) (1 two)))) #f)

  (test-equal (run
                 (term
                  (let ([o 1]
                        [t 2]
                        [r 3]
                        [f 4])
                    (((((λ (x)
                           (λ (y)
                              (λ (z)
                                 (λ (w)
                                    (+ (+ x y)
                                       (+ w z))))))
                        o)
                       t)
                      r)
                     f))))
                10)

  (test-equal (run (term
                      (let ([me (λ (x) x)])
                        (let ([tri
                               (λ (x)
                                  (let ([x1 (+ x -1)])
                                    (+ (me x1) x)))]
                              [five 5])
                          (tri five)))))
                9)

  (test-equal (run (term (let ([tri
                                  (λ (x)
                                     (let ([x1 (+ x -1)])
                                       x))]
                                 [five 5])
                             (tri five))))
                5)

  (test-equal (run (term
                      (let ([Y (λ (f)
                                  (let ([g (λ (x)
                                              (let ([xx (x x)])
                                                (f xx)))])
                                    (g g)))]
                            [tri
                             (λ (me)
                                (λ (x)
                                   (if0 x
                                        0
                                        (let ([x1 (+ x -1)])
                                          (+ (me x1) x)))))]
                            [five 5])
                        ((Y tri) five))))
                (+ 5 4 3 2 1 0))


  (test-equal (run (term (let ([one 1] [two 2])
                             (((λ (x) (λ (x) (+ x one))) one) two))))
                3)

  (test-results))
