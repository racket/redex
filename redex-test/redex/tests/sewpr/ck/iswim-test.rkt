#lang scheme

#|

This file carefully wraps a parameterize outside of the EXAMPLE
but around the calls to tests and then puts that code *before* ENDDEFS
so that it will be seen by test-results, but so that the individual test 
outputs won't show up when building the 'results' EXAMPLE.

Also note that that this means that the example tests will be prefixed to
each of the tests in all of the generated code, but again their output
won't show up either, only the one (duplicated) test case shows up.

This is a hack.

Don't add things to this file unless they need to fit into that hack somehow.

|#


(require scheme/port)
(require "../iswim/iswim.rkt" redex)


(parameterize ([current-output-port (open-output-nowhere)])
  (test-results)) ;; clear out the counters from previous tests

(parameterize ([current-error-port (open-output-nowhere)])
  
  ;; EXAMPLE red
  (test-->> iswim-red
            (term ((λ x (+ x x)) 2))
            (term 4))
  ;; STOP red
  
  ;; EXAMPLE fail
  (test-->> iswim-red
            (term ((λ x (- x x)) 2))
            (term 4))
  ;; STOP fail
  
  ;; EXAMPLE mf
  (test-equal (term (δ (+ 1 2))) (term 3))
  ;; STOP mf
  
  ;; EXAMPLE mf-fail
  (test-equal (term (δ (iszero 0))) (term (λ x (λ y y))))
  ;; STOP mf-fail
  )
;; ENDDEFS

;; EXAMPLE results
(test-results)
;; STOP results

