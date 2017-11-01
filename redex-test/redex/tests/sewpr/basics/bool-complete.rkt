;; START all
#lang scheme

(require redex)

(define-language bool-lang
  [B true
     false
     (∨ B B)]
  [C (∨ C B)
     (∨ B C)
     hole])

(define bool-red
  (reduction-relation
   bool-lang
   (--> (in-hole C (∨ true B))
        (in-hole C true)
        ∨-false)
   (--> (in-hole C (∨ false B))
        (in-hole C B)
        ∨-true)))

;; STOP all
(module+ main
;; START all
(traces bool-red
        (term (∨ (∨ true false) (∨ true true))))
;; STOP all
)

(provide bool-red)
