#lang scheme
(require redex "iswim.rkt")

(test-->> iswim-red
          (term (iszero 0))
          (term (λ x (λ y x))))
(test-->> iswim-red
          (term (iszero 1))
          (term (λ x (λ y y))))
(test-->> iswim-red
          (term (+ 1 2))
          (term 3))
(test-->> iswim-red
          (term ((λ x (+ x x)) 2))
          (term 4))

(test-->> iswim-red
          (term (+ (+ 1 2) (+ 3 4)))
          (term 10))

(test-->> iswim-red
          (term (* (* (* 2 3) 4) 5))
          120)

(test-->> iswim-red
          (term (↑ (↑ (↑ 2 3) 4) 5))
          1152921504606846976)

(test-->> iswim-red
          (term (↑ 3 3))
          27)

(test-->> iswim-red
          (term ((((iszero 1)
                   (λ d 2))
                  (λ d 3))
                 0))
          3)
(test-->> iswim-red
          (term ((((iszero 0)
                   (λ d 2))
                  (λ d 3))
                 0))
          2)

;; make sure the δ rule doesn't fire here.
(test-->> iswim-red
          (term (+ (λ x x) (λ y y)))
          (term (+ (λ x x) (λ y y))))

(test-->> iswim-red
          (term (add1 (sub1 0)))
          (term 0))

(test-->> iswim-red
          (term (add1 73))
          (term 74))
(test-->> iswim-red
          (term (sub1 73))
          (term 72))

(test-->> iswim-red
          (term (+ (λ x x) (+ 1 2)))
          (term (+ (λ x x) 3)))

(test-equal (term (subst x x y)) (term y))
(test-equal (term (subst z x y)) (term z))
(test-equal (term (subst (x (y z)) x y)) (term (y (y z))))
(test-equal (term (subst (λ x x) x y)) (term (λ x x)))
(test-equal (term (subst ((λ x x) ((λ y1 y1) (λ x z))) x y))
            (term ((λ x x) ((λ y2 y2) (λ x z)))))
(test-equal (term (subst (λ y x) x (λ z y)))
            (term (λ y1 (λ z y))))
(test-equal (term (subst (λ y x) x 1))
            (term (λ y 1)))
(test-equal (term (subst (λ y x) x y))
            (term (λ y1 y)))
(test-equal (term (subst (λ z (z2 z)) x (λ y y)))
            (term (λ z1 (z2 z1))))
(test-equal (term (subst (λ z (z1 z)) x (λ z z)))
            (term (λ z2 (z1 z2))))
(test-equal (term (subst (λ z (z1 z)) x z))
            (term (λ z2 (z1 z2))))
(test-equal (term (subst (λ x2 x2) x3 5))
            (term (λ x1 x1)))
(test-equal (term (subst (λ x1 x1) x2 z))
            (term (λ x3 x3)))
(test-results)
