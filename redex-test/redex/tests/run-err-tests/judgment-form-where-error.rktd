(#rx"where/error did not match"
 ([premise-pat (any_1 any_2 any_3)]) ()
 (let ()
   (define-language L)
   (define-judgment-form L 
     #:mode (J I)
     [(where/error premise-pat any)
      ----------
      (J any)])
   (judgment-holds (J 1))
   #f))
