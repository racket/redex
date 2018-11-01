("reduction-relation: relation not defined for #f"
 ([bad-test (test--> inc (term #f) (term #t))])
 (let ()
   (define-language L)
   (define inc
     (reduction-relation
      L #:domain integer
      (--> integer ,(add1 (term integer)))))
   bad-test))

("reduction-relation: relation not defined for #f"
 ([bad-test (test-->> inc (term #f) (term #t))])
 (let ()
   (define-language L)
   (define inc
     (reduction-relation
      L #:domain integer
      (--> integer ,(add1 (term integer)))))
   bad-test))

("reduction-relation: relation not defined for #f"
 ([bad-test (test-->>∃ inc (term #f) (term #t))])
 (let ()
   (define-language L)
   (define inc
     (reduction-relation
      L #:domain integer
      (--> integer ,(add1 (term integer)))))
   bad-test))
