#lang racket
(require redex)

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
  
  (Γ Δ Θ ::= · (Γ x ↦ e)))

(define-judgment-form L
  #:mode (⇓ I I O O)
  #:contract (⇓ Γ e Δ v)
  
  
  [----------- Value
   (⇓ Γ v Γ v)]
  
  
  [(⇓ Γ e Δ (λ (y) e_*))
   (⇓ Δ (subst e_* y x) Θ v)
   ------------------------- Application
   (⇓ Γ (e x) Θ v)]
  
  
  [(where (Γ x ↦ e) (separate Γ_* x))
   (⇓ Γ e Δ v)
   (where Δ_* (Δ x ↦ v))
   ---------------------------------- Variable
   (⇓ Γ_* x Δ_* (^ Δ_* v))]
  
  
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

(define-metafunction L
  subst : e x y -> e
  [(subst e x y) 
   (subst/no-avoid (rename-bound e y y_*) x y)
   (where y_* ,(variable-not-in (term (e x y)) (term y)))])

;; renames bound occurrences of 'x' to 'y'
;; makes sense only when 'y' doesn't appear in 'e'
(define-metafunction L
  rename-bound : e x y -> e
  [(rename-bound i x y) i]
  [(rename-bound (λ (x) e) x y) (λ (y) (rename-all e x y))]
  [(rename-bound (λ (z) e) x y) (λ (z) (rename-bound e x y))]
  [(rename-bound (e z) x y) ((rename-bound e x y) z)]
  [(rename-bound (let ([x_* e_*] ... [x e] [x_** e_**] ...) e_***) x y)
   (let ([x_* (rename-bound e_* x y)] ...
         [y (rename-bound e x y)]
         [x_** (rename-bound e_** x y)] ...)
     (rename-all e_*** x y))]
  [(rename-bound (let ([z e] ...) e_*) x y)
   (let ([z (rename-bound e x y)] ...) (rename-bound e_* x y))]
  [(rename-bound z x y) z]
  [(rename-bound (+ e_1 e_2) x y) (+ (rename-bound e_1 x y) (rename-bound e_2 x y))]
  [(rename-bound (if0 e_1 e_2 e_3) x y)
   (if0 (rename-bound e_1 x y)
        (rename-bound e_2 x y)
        (rename-bound e_3 x y))])

(define-metafunction L
  subst/no-avoid : e x y -> e
  [(subst/no-avoid i x y) i]
  [(subst/no-avoid (λ (x) e) x y) (λ (x) e)]
  [(subst/no-avoid (λ (z) e) x y) (λ (z) (subst/no-avoid e x y))]
  [(subst/no-avoid (e z) x y) ((subst/no-avoid e x y) (subst/no-avoid z x y))]
  [(subst/no-avoid (let ([z e] ... [x e_*] [z_** e_**] ...) e_***) x y)
   (let ([z (subst/no-avoid e x y)] ...
         [x (subst/no-avoid e_* x y)]
         [z_** (subst/no-avoid e_** x y)] ...)
     e_***)]
  [(subst/no-avoid (let ([z e] ...) e_**) x y)
   (let ([z (subst/no-avoid e x y)] ...)
     (subst/no-avoid e_** x y))]
  [(subst/no-avoid x x y) y]
  [(subst/no-avoid z x y) z]
  [(subst/no-avoid (+ e_1 e_2) x y) (+ (subst/no-avoid e_1 x y) (subst/no-avoid e_2 x y))]
  [(subst/no-avoid (if0 e_1 e_2 e_3) x y)
   (if0 (subst/no-avoid e_1 x y)
        (subst/no-avoid e_2 x y)
        (subst/no-avoid e_3 x y))])

;; renames all occurrences of 'x' to 'y'
(define-metafunction L
  rename-all : any x y -> any
  [(rename-all x x y) y]
  [(rename-all z x y) z]
  [(rename-all (any ...) x y) ((rename-all any x y) ...)]
  [(rename-all any x y) any])

;; The ^ function freshens all of the bound
;; variables in the 'e' argument, making sure
;; that none of the new variables appear in Δ.
;; For example, (λ (x) x) turns into (λ (x1) x1)
;; (assuming that x appears in Δ).
;; The function is part of preserving the invariant
;; that there are no duplicate variables bound
;; in the environment in the first and third
;; positions in the semantics.
(define-metafunction L
  ^ : Δ e -> e
  [(^ Δ e) 
   e_*
   (where (e_* (x ...)) (^/h Δ e ()))])

(define-metafunction L
  ^/h : Δ e (z ...) -> (e (z ...))
  [(^/h Δ i (z ...)) (i (z ...))]
  [(^/h Δ (λ (x) e) (z ...))
   ((λ (y) e_*) (z_* ...))
   (where y ,(variable-not-in (term (Δ z ...)) (term x)))
   (where (e_* (z_* ...)) (^/h Δ (replace-free e (x y)) (y z ...)))]
  [(^/h Δ (e x) (z ...))
   ((e_* x_*) (z ...))
   (where (e_* (z_* ...)) (^/h Δ e (z ...)))
   (where (x_* (z_** ...)) (^/h Δ x (z_* ...)))]
  [(^/h Δ (let () e) (z ...))
   ((let () e_*) (z_* ...))
   (where (e_* (z_* ...)) (^/h Δ e (z ...)))]
  [(^/h Δ (let ([x_1 e_1] [x_2 e_2] ...) e) (z ...))
   ((let ([y_1 e_1*] [x_2* e_2*] ...) e_*) (z_** ...))
   (where y_1 ,(variable-not-in (term (Δ z ...)) (term x_1)))
   (where ((let ([x_2* e_2*] ...) e_*) (z_* ...))
          (^/h Δ (let ([x_2 e_2] ...) (replace-free e (x_1 y_1))) (y_1 z ...)))
   (where (e_1* (z_** ...)) (^/h Δ e_1 (z_* ...)))]
  [(^/h Δ x (z ...)) (x (z ...))]
  [(^/h Δ (+ e_1 e_2) (z ...))
   ((+ e_1* e_2*) (z_** ...))
   (where (e_1* (z_* ...)) (^/h Δ e_1 (z ...)))
   (where (e_2* (z_** ...)) (^/h Δ e_2 (z_* ...)))]
  [(^/h Δ (if0 e_1 e_2 e_3) (z ...))
   ((if0 e_1* e_2* e_3*) (z_* ...))
   (where ((+ (+ e_1* e_2*) e_3*) (z_* ...)) (^/h Δ (+ (+ e_1 e_2) e_3) (z ...)))])

(define-metafunction L
  replace-free : e (x y) ... -> e
  [(replace-free i (x y) ...) i]
  [(replace-free (λ (x) e) (x_* y_*) ... (x y) (x_** y_**) ...)
   (replace-free (λ (x) e) (x_* y_*) ... (x_** y_**) ...)]
  [(replace-free (λ (z) e) (x y) ...) (λ (z) (replace-free e (x y) ...))]
  [(replace-free (e z) (x y) ...)
   ((replace-free e (x y) ...) (replace-free z (x y) ...))]
  [(replace-free (let ([z e] ...) e_*) (x y) ...)
   (let ([z (replace-free e (x y) ...)] ...)
     (replace-free e_* (x_2 y_2) ...))
   (where ((x_2 y_2) ...) (remove-used-bindings ((x y) ...) (z ...)))]
  [(replace-free x (x_1 x_2) ... (x y) (x_3 x_4) ...) y]
  [(replace-free z (x y) ...) z]
  [(replace-free (+ e_1 e_2) (x y) ...)
   (+ (replace-free e_1 (x y) ...) (replace-free e_2 (x y) ...))]
  [(replace-free (if0 e_1 e_2 e_3) (x y) ...)
   (if0 (replace-free e_1 (x y) ...) 
        (replace-free e_2 (x y) ...)
        (replace-free e_3 (x y) ...))])

(define-metafunction L
  [(remove-used-bindings ((x_1 y_1) ... (x_2 y_2) (x_3 y_3) ...)
                         (x_4 ... x_2 x_5 ...))
   (remove-used-bindings ((x_1 y_1) ... (x_3 y_3) ...)
                         (x_4 ... x_2 x_5 ...))]
  [(remove-used-bindings ((x y) ...) 
                         (z ...))
   ((x y) ...)])

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
  
  (test-equal (term (replace-free (let ([x x] [p q]) x) (x y)))
              (term (let ([x y] [p q]) x)))
  (test-equal (term (replace-free (let ([p q]) x) (x y)))
              (term (let ([p q]) y)))
  (test-equal (term (replace-free (λ (x) y) (y z)))
              (term (λ (x) z)))
  (test-equal (term (replace-free (λ (y) y) (y z)))
              (term (λ (y) y)))
  (test-equal (term (replace-free (if0 x y z) (y z)))
              (term (if0 x z z)))
  
  (test-equal (term (rename-bound (λ (x) x) x y))
              (term (λ (y) y)))
  (test-equal (term (rename-bound (λ (y) x) x y))
              (term (λ (y) x)))
  (test-equal (term (rename-bound (λ (x) (λ (x) x)) x y))
              (term (λ (y) (λ (y) y))))
  (test-equal (term (rename-bound (let ([x 1] [y 2]) x) x z))
              (term (let ([z 1] [y 2]) z)))
  
  (test-equal (term (subst (λ (x) ((λ (y) x) y)) y z))
              (term (λ (x) ((λ (y) x) z))))
  (test-equal (term (subst (λ (x) ((λ (y) y) y)) y z))
              (term (λ (x) ((λ (y) y) z))))
  (test-equal (term (subst (λ (x) ((λ (q) y) y)) y z))
              (term (λ (x) ((λ (q) z) z))))
  (test-equal (term (subst (λ (y) x) x y))
              (term (λ (y1) y)))
  (test-equal (term (subst (let ([x 1]) (+ x z)) z q))
              (term (let ([x 1]) (+ x q))))
  (test-equal (term (subst (let ([x 1][y 2][z 3]) (+ x y)) x q))
              (term (let ([x 1][y 2][z 3]) (+ x y))))
  
  (test-equal (term (separate · x)) (term ⊥))
  (test-equal (term (separate (· x ↦ 1) x)) (term (· x ↦ 1)))
  (test-equal (term (separate ((· x ↦ 1) y ↦ 2) x)) 
              (term ((· y ↦ 2) x ↦ 1)))
  (test-equal (term (separate (· x ↦ 1) y)) (term ⊥))
  
  (test-equal (term (^ (· x ↦ (λ (x) x)) (λ (x) x))) 
              (term (λ (x1) x1)))
  (test-equal (term (^ · (λ (x) (λ (y) (x y))))) 
              (term (λ (x) (λ (y) (x y)))))
  (test-equal (term (^ (· x ↦ y) (let ([x 1] [y 2]) x)))
              (term (let ([x1 1] [y1 2]) x1)))
  (test-equal (term (^ (· x ↦ x1) (λ (x) (+ x y))))
              (term (λ (x2) (+ x2 y))))
  (test-equal (term (^ (· tri ↦ (λ (x) (let ((x1 x)) x1)))
                       (λ (x) (let ((x1 x)) x1))))
              (term (λ (x2) (let ((x3 x2)) x3))))
  (test-equal (term (^ (· x ↦ 1)
                       (let ([x (let ([x 1]) x)])
                         (let ([x (let ([x 2]) x)])
                           x))))
              (term (let ([x1 (let ([x4 1]) x4)])
                      (let ([x2 (let ([x3 2]) x3)])
                        x2))))
  (test-equal (term (^ (· x ↦ 1)
                       (if0 x (λ (x) x) x)))
              (term (if0 x (λ (x1) x1) x)))
  
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
  
  (test-results))
