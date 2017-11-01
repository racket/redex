#lang scheme
(require redex)

(require "bool-any.rkt")

(test-->> bool-any-red
          (term (∨ true true))
          (term true))
(test-->> bool-any-red
          (term (∨ false true))
          (term true))
(test-->> bool-any-red
          (term (∨ true false))
          (term true))
(test-->> bool-any-red
          (term (∨ false false))
          (term false))
(test-->> bool-any-red
          (term (∨ (∨ true false) (∨ true false)))
          (term true))
(test-->> bool-any-red
          (term (∨ (∨ false false) (∨ false false)))
          (term false))

(test-predicate values (redex-match bool-any-lang B B1))
(test-predicate values (redex-match bool-any-lang B B2))
(test-predicate values (redex-match bool-any-lang B B3))
(test-predicate values (redex-match bool-any-lang B B4))
(test-predicate values (redex-match bool-any-lang B B5))

(test-predicate values (redex-match bool-any-lang C C1))
(test-predicate values (redex-match bool-any-lang C C2))
(test-predicate values (redex-match bool-any-lang C C3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require "bool-standard.rkt")

(test-->> bool-standard-red
          (term (∨ true true))
          (term true))
(test-->> bool-standard-red
          (term (∨ false true))
          (term true))
(test-->> bool-standard-red
          (term (∨ true false))
          (term true))
(test-->> bool-standard-red
          (term (∨ false false))
          (term false))
(test-->> bool-standard-red
          (term (∨ (∨ true false) (∨ true false)))
          (term true))
(test-->> bool-standard-red
          (term (∨ (∨ false false) (∨ false false)))
          (term false))

(test-predicate values (redex-match bool-standard-lang E E1))
(test-predicate values (redex-match bool-standard-lang E E2))
(test-predicate values (redex-match bool-standard-lang E E3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require "bool-complete.rkt")

(test-->> bool-red
          (term (∨ true true))
          (term true))
(test-->> bool-red
          (term (∨ false true))
          (term true))
(test-->> bool-red
          (term (∨ true false))
          (term true))
(test-->> bool-red
          (term (∨ false false))
          (term false))
(test-->> bool-red
          (term (∨ (∨ true false) (∨ true false)))
          (term true))
(test-->> bool-red
          (term (∨ (∨ false false) (∨ false false)))
          (term false))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-results)
