#lang racket

(parameterize ([current-namespace (make-base-namespace)])
              (eval '(require errortrace))
              (eval '(require racket/pretty))
              (eval '(lambda (x) asdf))
              (eval '(require redex/reduction-semantics))
              (eval '(pretty-print (syntax->datum (expand-once #'(define-language L)))))
              (eval '(define-language L))
              #;(eval '(define-judgment-form L
                       #:mode (J I)
                       [(J a)
                        (J b)]
                       [(J b)])))
