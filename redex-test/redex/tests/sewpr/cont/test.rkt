#lang racket/base
(require redex/reduction-semantics "cont.rkt")

(test-equal (with-handlers ((exn? (λ (x) 'err)))
              (apply-reduction-relation* ☠-iswim-red (term (+ 42 (call/cc (λ k (k 1)))))))
            'err)
(test-equal (with-handlers ((exn? (λ (x) 'err)))
              (redex-match ☠-iswim (in-hole E any) (term (+ 42 ((λ k (k 1)) (cont 1))))))
            'err)


(test-->> c-iswim-red
          (term (call/cc (λ k (k 1))))
          1)
(test-->> ☺-iswim-red
          (term (call/cc (λ k (k 1))))
          1)
(test-->> c-iswim-red
          (term (+ 1 (call/cc (λ k (+ (λ y y) (k 12))))))
          13)
(test-->> ☺-iswim-red
          (term (+ 1 (call/cc (λ k (+ (λ y y) (k 12))))))
          13)

(test-->> c-iswim-red
          (term (+ 1 (call/cc ((λ x x) (λ k 1)))))
          2)

(test-->> ☺-iswim-red
          (term (+ 1 (call/cc ((λ x x) (λ k 1)))))
          2)

(test-results)
