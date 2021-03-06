(#rx"expected the name of the relation"
 ([bad-def (define-relation syn-err-lang R)])
 bad-def)

(#rx"expected a sequence of patterns separated by"
 ([subset ⊂])
 (define-relation syn-err-lang R subset))

(#rx"expected clause definitions"
 ([bad-def (define-relation syn-err-lang foo ⊆ c)])
 bad-def)

(#rx"expected a pattern"
 ([cross ×])
 (define-relation syn-err-lang foo ⊆ c cross))

(#rx"found a 'where' clause not at the end"
 ([first-where (where any_c any_a)]
  [first-post-where (R () ())])
 (define-relation syn-err-lang
   [(R () ())]
   [(R (any_a) (any_b)) 
    (R any_c any_d) 
    first-where
    (where any_d any_b)
    first-post-where]))

(#rx"expected an identifier in the language position"
 ([not-lang [(R a)]])
 (define-relation not-lang))

(#rx"mode specifies a binary relation but use supplied 3 terms"
 ([wrong-arity (J2 natural_1 natural_2 0)])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J2 I O)

     [------------
      (J2 any any)])

   (define-relation syn-err-lang
     R ⊂ any × any

     [(R natural_1 natural_2)
      wrong-arity])

   (void)))
