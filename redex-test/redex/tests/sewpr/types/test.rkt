#lang racket/base
(require redex/reduction-semantics "types.rkt")

(test-equal (term (TC () 1))
            (term num))

(test-equal (term (TC () (+ 2 3)))
            (term num))

(test-equal (term (TC () (+ (* 1 2) 3)))
            (term num))

(test-equal (term (TC () (+ 1 (iszero 1))))
            (term #f))

(test-equal (term (TC () (λ X num X)))
            (term (-> num num)))

(test-equal (term (TC () x))
            (term #f))

(test-equal (term (TC () (λ X num x)))
            (term #f))

(test-equal (term (TC () (λ X (-> num num) (λ X num X))))
            (term (-> (-> num num) (-> num num))))

(test-equal (term (TC () ((λ X num X) 1)))
            (term num))
(test-equal (term (TC () ((λ X num X) y)))
            (term #f))
(test-equal (term (TC () (1 1)))
            (term #f))
(test-equal (term (TC () (x 1)))
            (term #f))

(test-equal (term (TC ()
                      (((λ x num (λ y num x)) 
                        (+ ((λ x num x) 1) 2))
                       3)))
            (term num))

(test-equal (term (t-subst (λ x num (λ y num z)) z 1))
            (term (λ x num (λ y num 1))))
(test-equal (term (t-subst (x z y z) z 1))
            (term (x 1 y 1)))
(test-equal (term (t-subst (x (λ z num z) y z) z 1))
            (term (x (λ z num z) y 1)))

(test-equal (term (∆ (iszero num)))
            (term (-> num (-> num num))))
(test-equal (term (∆ (iszero (-> num num))))
            (term #f))
(test-equal (term (∆ (add1 num)))
            (term num))
(test-equal (term (∆ (sub1 num)))
            (term num))

(test-->> t-iswim-red
          (term (+ 1 2))
          3)
(test-->> t-iswim-red
          (term ((λ x num x) 1))
          1)

;; this test tests that t-iswim-red is actually broken.
(test-->> t-iswim-red
          (term (((λ x num (λ y num (+ x y))) 1) 2))
          (term (1 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (prefix-in e: "types-exn.rkt"))


(test-equal (term (e:TC () 1))
            (term num))

(test-equal (term (e:TC () (+ 2 3)))
            (term num))

(test-equal (term (e:TC () (+ (* 1 2) 3)))
            (term num))

(define-syntax test-exn
  (syntax-rules ()
    [(_ expr) (with-handlers ((exn:fail:redex? void)
                              (exn? (lambda (x) (printf "exn-test failed: ~a \n" 'expr))))
                expr
                (void))]))

(test-exn (term (e:TC () (+ 1 (iszero 1)))))

(test-equal (term (e:TC () (λ X num X)))
            (term (-> num num)))

(test-exn (term (e:TC () x)))

(test-exn (term (e:TC () (λ X num x))))

(test-equal (term (e:TC () (λ X (-> num num) (λ X num X))))
            (term (-> (-> num num) (-> num num))))

(test-equal (term (e:TC () ((λ X num X) 1)))
            (term num))
(test-exn (term (e:TC () ((λ X num X) y))))
(test-exn (term (e:TC () (1 1))))
(test-exn (term (e:TC () (x 1))))

(test-exn (term (e:TC () (+ x y))))

(test-exn (term (e:TC ()
                      (((λ x num (λ y num x)) 
                        (+ ((λ x num x) 1) 2))
                       3))))

(test-->> e:t-iswim-red
          (term (+ 1 2))
          3)
(test-->> e:t-iswim-red
          (term ((λ x num x) 1))
          1)

;; this test tests that e:t-iswim-red is actually broken.
(test-->> e:t-iswim-red
          (term (((λ x num (λ y num (+ x y))) 1) 2))
          (term (1 2)))

(test-results)
