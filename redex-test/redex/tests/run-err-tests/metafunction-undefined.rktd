("q: undefined;\n cannot use before initialization"
 ([use (term (q))]) ([def q])
 (let ()
   use ;; it would be better if this pointed to the metafunction inside the `term` (and it does seem to in DrRacket!)
   (define-language L)
   (define-metafunction L
     [(def) ()])
   #f))
