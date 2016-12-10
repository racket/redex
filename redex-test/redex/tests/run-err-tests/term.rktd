(#rx"incompatible ellipsis match counts"
 ([the-body (term (((x y) ...) ...))])
 ([xlhs (x ...)] [ylhs ((y ...) ...)])
 (term-let ([xlhs '(a b c)]
            [ylhs '((1 2) (4 5 6) (7 8 9))])
           the-body))

(#rx"incompatible ellipsis match counts"
 ([body (term ((((f x) y) ...) ...))])
 ([fn f] [xlhs (x ...)] [ylhs ((y ...) ...)])
 (term-let-fn ([fn car])
              (term-let ([xlhs '(a b c)]
                         [ylhs '((1 2) (4 5 6) (7 8 9))])
                        body)))

(#rx"incompatible ellipsis match counts"
 ([body (term (f ((x y) ...)))])
 ([fn f] [xlhs (x ...)] [ylhs (y ...)])
 (term-let-fn ([fn car])
              (term-let ([xlhs '(a b)]
                         [ylhs '(c d e)])
                        body)))

(#rx"incompatible ellipsis match counts"
 ([app (term ((f (x y)) ...))])
 ([fn f] [xlhs (x ...)] [ylhs (y ...)] [ellipsis ...])
 (term-let-fn ([fn car])
              (term-let ([xlhs '(a b)]
                         [ylhs '(c d e)])
                        app)))

(#rx"incompatible ellipsis match counts"
 ([plug (term ((in-hole hole (x y)) ...))])
 ([xlhs (x ...)] [ylhs (y ...)] [ellipsis ...])
 (term-let-fn ([fn car])
              (term-let ([xlhs '(a b)]
                         [ylhs '(c d e)])
                        plug)))

(#rx"term .* does not match pattern"
 ([rhs 'a]) ([ellipsis ...])
 (term-let ([(x ellipsis) rhs]) 3))

("x: undefined;\n cannot use before initialization"
 ([use x]) ([def x])
 (let ()
   (define t (term (use y)))
   (define-term def z)
   t))
