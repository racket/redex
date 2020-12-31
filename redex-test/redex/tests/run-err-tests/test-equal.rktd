("bang"
 ([bad-test (test-equal #f #f)])
 (parameterize ([default-equiv (λ (x y) (error "bang"))])
   bad-test))
