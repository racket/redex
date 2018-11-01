("bang"
 ([bad-test (test-equal #f #f)])
 (parameterize ([default-equiv (λ (a b) (error "bang"))])
   bad-test))
