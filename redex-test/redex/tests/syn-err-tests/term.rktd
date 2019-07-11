(#rx"missing ellipsis"
 ([id-no-ellipsis x]) ([ellipsis ...])
 (term-let ([(id-no-ellipsis ellipsis) '(a b c)]) (term id-no-ellipsis)))

(#rx"too few ellipses"
 ([bound x]) ([bind x])
 (... (term-let ([((bind ...) ...) '()])
                (term (bound ...)))))

(#rx"modeless judgment forms disallowed"
 ([use-of-J (J 1 2)]) ()
 (let ()
   (define-language L)
   (define-judgment-form L
     [-----
      (J any any)])
   (term (λ (x) use-of-J))))
