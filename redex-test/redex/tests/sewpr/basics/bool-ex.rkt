#lang scheme
(require redex "bool-standard.rkt" "bool-any.rkt")

;; ENDDEFS

(module+ main
;; START lang-traces
(traces bool-any-red
        (term (∨ (∨ true false) (∨ true true))))
;; STOP lang-traces
)

;; EXAMPLE test-B
(redex-match bool-any-lang 
             B 
             (term (∨ false true)))
;; STOP test-B

;; EXAMPLE test-multiple
(redex-match bool-any-lang 
             (in-hole C (∨ true B)) 
             (term (∨ true (∨ true false))))
;; STOP test-multiple

;; EXAMPLE test-red
(redex-match bool-any-lang 
             (in-hole C (∨ true B)) 
             (term (∨ (∨ true (∨ false true)) false)))
;; STOP test-red

(module+ main
;; START traces
(traces bool-standard-red
        (term (∨ (∨ true false) (∨ true true))))
;; STOP traces
)
