#lang scheme
(require redex "eiswim.rkt")

(test-->> e-iswim-red
          (term
           (/ ((λ x (/ 1 x)) 7)
              2))
          1/14)

(test-->> e-iswim-red
          (term
           (((λ x (λ y (+ x y))) 1) 2))
          3)

(test-->> e-iswim-red
          (term (iszero 0))
          (term (λ x (λ y x))))
(test-->> e-iswim-red
          (term (iszero 1))
          (term (λ x (λ y y))))
(test-->> e-iswim-red
          (term (+ 1 2))
          (term 3))
(test-->> e-iswim-red
          (term ((λ x (+ x x)) 2))
          (term 4))

(test-->> e-iswim-red
          (term (+ (+ 1 2) (+ 3 4)))
          (term 10))

(test-->> e-iswim-red
          (term (* (* (* 2 3) 4) 5))
          120)

(test-->> e-iswim-red
          (term (↑ (↑ (↑ 2 3) 4) 5))
          1152921504606846976)

(test-->> e-iswim-red
          (term (↑ 3 3))
          27)

(test-->> e-iswim-red
          (term ((((iszero 1)
                   (λ d 2))
                  (λ d 3))
                 0))
          3)
(test-->> e-iswim-red
          (term ((((iszero 0)
                   (λ d 2))
                  (λ d 3))
                 0))
          2)

(test-->> e-iswim-red
          (term (+ (λ x x) (λ y y)))
          (term (err 1)))

(test-->> e-iswim-red
          (term (add1 (sub1 0)))
          (term 0))

(test-->> e-iswim-red
          (term (add1 73))
          (term 74))
(test-->> e-iswim-red
          (term (sub1 73))
          (term 72))

(test-->> e-iswim-red
          (term (+ (+ 1 2) (λ x x)))
          (term (err 2)))

(test-->> e-iswim-red
          (term (+ (+ 1 (err 2)) (err 3)))
          (term (err 2)))

(test-->> e-iswim-red
          (term (+ (((λ x x) 17) 2) 1))
          (term (err 17)))

(test-->> e-iswim-red
          (term (/ 1 2))
          (term 1/2))


(test-->> e-iswim-red2
          (term (iszero 0))
          (term (λ x (λ y x))))
(test-->> e-iswim-red2
          (term (iszero 1))
          (term (λ x (λ y y))))
(test-->> e-iswim-red2
          (term (+ 1 2))
          (term 3))
(test-->> e-iswim-red2
          (term ((λ x (+ x x)) 2))
          (term 4))

(test-->> e-iswim-red2
          (term (+ (+ 1 2) (+ 3 4)))
          (term 10))

(test-->> e-iswim-red2
          (term (* (* (* 2 3) 4) 5))
          120)

(test-->> e-iswim-red2
          (term (↑ (↑ (↑ 2 3) 4) 5))
          1152921504606846976)

(test-->> e-iswim-red2
          (term (↑ 3 3))
          27)

(test-->> e-iswim-red2
          (term ((((iszero 1)
                   (λ d 2))
                  (λ d 3))
                 0))
          3)
(test-->> e-iswim-red2
          (term ((((iszero 0)
                   (λ d 2))
                  (λ d 3))
                 0))
          2)

(test-->> e-iswim-red2
          (term (+ (λ x x) (λ y y)))
          (term (err 1)))

(test-->> e-iswim-red2
          (term (add1 (sub1 0)))
          (term 0))

(test-->> e-iswim-red2
          (term (add1 73))
          (term 74))
(test-->> e-iswim-red2
          (term (sub1 73))
          (term 72))

(test-->> e-iswim-red2
          (term (+ (+ 1 2) (λ x x)))
          (term (err 2)))

(test-->> e-iswim-red2
          (term (+ (+ 1 (err 2)) (err 3)))
          (term (err 2)))

(test-->> e-iswim-red2
          (term (+ (((λ x x) 17) 2) 1))
          (term (err 17)))

(test-->> e-iswim-red2
          (term (/ 1 2))
          (term 1/2))

(test-results)
