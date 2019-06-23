(#rx"expected a judgment form name"
 ([not-judgment-form junk])
 (judgment-holds (not-judgment-form z (s z))))

(#rx"a[?]: mode specifies a unary relation but use supplied 2 terms"
 ([bad-judgment (a? a q)])
 ([name a?])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (name I)
     [(name a)])
   (judgment-holds bad-judgment)))

(#rx"mode specifies a binary relation but use supplied 1 term"
 ([bad-judgment (test Z)])
 ()
 (let ()
   (define-language nats
     (nat Z (S Z)))
   
   (define-judgment-form nats
     #:mode (test I O)
     [---------
      (test nat one)])
   
   (test-judgment-holds
    bad-judgment)))
