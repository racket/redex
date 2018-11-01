(#rx"missing ellipsis"
 ([id-no-ellipsis x])
 (term-let ([(id-no-ellipsis ...) '(a b c)]) (term id-no-ellipsis)))

(#rx"too few ellipses"
 ([bound x]) ([bind x])
 (term-let ([((bind ...) ...) '()])
           (term (bound ...))))
