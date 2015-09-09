#lang racket
(require "test-util.rkt"
         redex/reduction-semantics
         (only-in redex/private/lang-struct make-bindings make-bind)
         racket/match
         racket/trace
         redex/private/struct)

(module test racket/base)

(reset-count)

(define-language empty-language)

(define-syntax-rule 
  (capture-output arg1 args ...)
  (let ([p (open-output-string)])
    (parameterize ([current-output-port p]
                   [current-error-port p])
      arg1 args ...)
    (get-output-string p)))

(let ()
  (define red (reduction-relation empty-language (--> 1 2)))
  (test (capture-output (test-->> red 1 2) (test-results))
        "One test passed.\n")
  (test (capture-output (test-->> red 2 3) (test-results))
        #rx"FAILED .*tl-test.(?:.+):[0-9.]+\nexpected: 3\n  actual: 2\n1 test failed \\(out of 1 total\\).\n"))

(let ()
  (define red-share (reduction-relation 
                     empty-language
                     (--> a b)
                     (--> a c)
                     (--> c d)
                     (--> b d)))
  (test (capture-output (test-->> red-share (term a) (term d)) (test-results))
        "One test passed.\n"))

(let ()
  (define red-cycle (reduction-relation 
                     empty-language
                     (--> a a)))
  (test (capture-output (test-->> red-cycle #:cycles-ok (term a)) (test-results))
        "One test passed.\n")
  (test (capture-output (test-->> red-cycle (term a)) (test-results))
        #rx"FAILED .*tl-test.(?:.+):[0-9.]+\nfound a cycle in the reduction graph\n1 test failed \\(out of 1 total\\).\n"))

(let ()
  (define subred (reduction-relation empty-language (--> natural ,(- (term natural) 1))))
  (test (capture-output (test-->> subred #:pred (λ (x) #t) 1 -1) (test-results))
        "One test passed.\n")
  (test (capture-output (test-->> subred #:pred number? 1 -1) (test-results))
        "One test passed.\n")
  (test (capture-output (test-->> subred #:pred odd? 1 -1) (test-results))
        #rx"FAILED .*tl-test.rkt:[0-9.]+\nfound a term that failed #:pred: 0\n1 test failed \\(out of 1 total\\).\n"))

(let ()
  (define-metafunction empty-language [(f any) ((any))])
  (test (capture-output (test-equal (term (f 1)) (term ((1))))
                        (test-results))
        "One test passed.\n"))

(let ()
  (define-metafunction empty-language [(f any) ((any))])
  (test (capture-output (test-equal (term (f 1)) (term ((2))))
                        (test-results))
        (regexp
         (regexp-quote
          "  actual: '((1))\nexpected: '((2))\n1 test failed (out of 1 total).\n"))))

(let ()
  (define-metafunction empty-language [(f any) any])
  (test (capture-output
         (test-equal (term (f ,(build-list 10 (λ (x) 'this-is-a-bit-longish))))
                     (term wrong))
         (test-results))
        (regexp
         (regexp-quote
          (string-append
           "actual:\n"
           (apply string-append
                  (for/list ([i (in-range 10)])
                    (string-append
                     (if (zero? i) "  '(" "    ")
                     "this-is-a-bit-longish"
                     (if (= i 9) ")\n" "\n"))))
           "expected: 'wrong\n"
           "1 test failed (out of 1 total).\n")))))

(let ()
  (define-metafunction empty-language [(f any) ((any))])
  (define (my-equal? x y) (and (memq x '(a b c)) (memq y '(a b c))))
  (test (capture-output (test-equal (term a) (term b) #:equiv my-equal?)
                        (test-results))
        "One test passed.\n"))

(let ()
  (test (capture-output (test-predicate odd? 1)
                        (test-results))
        "One test passed.\n"))

(let ()
  (define red (reduction-relation empty-language (--> any (any))))
  (test (capture-output (test--> red (term (1 2 3)) (term ((1 2 3)))) (test-results))
        "One test passed.\n"))

(let ()
  (define red (reduction-relation empty-language 
                                  (--> any (any))
                                  (--> (any) any)))
  (test (capture-output (test--> red (term (x)) (term ((x))) (term x)) (test-results))
        "One test passed.\n")
  (test (capture-output (test--> red (term (x)) (term x) (term ((x)))) (test-results))
        "One test passed.\n"))

(let ()
  (define-language L
    (i integer))
  
  (define R
    (reduction-relation
     L
     (--> i i)
     (--> i ,(add1 (term i)))))
  
  (define (mod2=? i j)
    (= (modulo i 2) (modulo j 2)))
  
  (test (capture-output (test--> R #:equiv mod2=? 7 1 0) (test-results))
        "One test passed.\n")
  (test (capture-output (test--> R #:equiv mod2=? 7 1) (test-results))
        #rx"FAILED .*tl-test\\.(?:.+):[0-9.]+\nexpected: 1\n  actual: 8\n  actual: 7\n1 test failed \\(out of 1 total\\).\n"))

(let-syntax ([test-bad-equiv-arg
              (λ (stx)
                (syntax-case stx ()
                  [(_ test-form)
                   (syntax/loc stx
                     (test-contract-violation
                      (test-form (reduction-relation empty-language (--> any any))
                                 #:equiv 1 2)
                      #:blaming "tl-test"))]))])
  (test-bad-equiv-arg test-->)
  (test-bad-equiv-arg test-->>))

(let ()
  (capture-output (test-results))
  (define-language L)
  
  (define 1+
    (reduction-relation 
     L
     (--> number ,(add1 (term number)))))
  
  (define (equal-to-7 x) (= x 7))
  (test (capture-output (test-->>∃ #:steps 5 1+ 0 equal-to-7))
        #rx"^FAILED .*\nno term satisfying #<procedure:equal-to-7> reachable from 0 \\(within 5 steps\\)\n$")
  
  (test (capture-output (test-->>∃ 1+ 0 7)) "")
  (test (capture-output (test-->>E 1+ 0 7)) "")
  (test (capture-output (test-->>∃ #:steps +inf.0 1+ 0 7)) "")
  (test (capture-output (test-->>∃ 1+ 0 equal-to-7)) "")
  
  (define identity
    (reduction-relation
     L
     (--> any any)))
  
  (test (capture-output (test-->>∃ identity 0 1))
        #rx"^FAILED .*\nterm 1 not reachable from 0\n$")
  
  (test (capture-output (test-results)) "2 tests failed (out of 6 total).\n")
  
  (test-contract-violation
   (test-->>∃ 1+ 0 (λ (x y) x))
   #:blaming "tl-test"
   #:message "goal expression")
  (test-contract-violation
   (test-->>∃ 1 0 1)
   #:blaming "tl-test"
   #:message "reduction relation expression")
  (test-contract-violation
   (test-->>∃ #:steps 1.1 1+ 0 1)
   #:blaming "tl-test"
   #:message "steps expression"))

(print-tests-passed 'tl-test.rkt)
