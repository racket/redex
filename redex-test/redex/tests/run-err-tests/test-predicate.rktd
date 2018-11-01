("bang"
 ([bad-test (test-predicate (λ (x) (error "bang")) #f)])
 bad-test)
