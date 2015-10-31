#lang racket

(module perf-test-tools racket
 (provide (all-defined-out))

 (define-syntax-rule (times n what)
   (let loop ([rpts n])
     (when (> rpts 0)
           what
           (loop (- rpts 1)))))

 (define-syntax-rule (perf-test (runner ...) t repeat-count)
   (begin
     (void ;; suppress printing...
      ;; but pre-run to make sure we've allocated enough space on the heap
      (begin (collect-garbage) ;; unclear why this is important here, but empirically, it seems to be
             (times 1 (apply runner t))) ...)

     (printf " ~a: ~a~n" 't (string-join (list (symbol->string 'runner) ...) " vs. "))

     (begin
       (printf "  ")
       (collect-garbage)
       (time (times repeat-count (apply runner t)))) ...)))





(module micro-tests racket
 (require redex)
 (require redex/private/binding-forms-compiler)
 (require redex/private/binding-forms-definitions)
 (require (submod ".." perf-test-tools))

 (printf "Microbenchmarks")

 (define-language L
   (e (bd x x))
   (x variable-not-otherwise-mentioned))

 (define-language binding:L
   (e (bd x x))
   (x variable-not-otherwise-mentioned)
   #:binding-forms
   (bd x x_body #:refers-to x))

 (define-syntax (bspec-of stx)
   (syntax-case stx ()
     [(form-name (all-nts ...) . bf-forms)
      #`(second (first #,(compile-binding-forms #`bf-forms
                                                (syntax->datum #`(all-nts ...))
                                                #`form-name)))]))


 (define bd-bspec (bspec-of (x e) (bd x x_body #:refers-to x)))
 (define bd-v-w-s
   (value-with-spec
    (match-bindings (first (redex-match L (bd x x_body) `(bd a a))))
    bd-bspec))
 (define bd-v-w-s-b-b
   (value-with-spec
    (match-bindings (first (redex-match L (bd x x_body) `(bd b b))))
    bd-bspec))


 (define (noop-match)
   (redex-match L
     (bd x x_body) `(bd y y)))

 (define (manual:freshen-match)
   (define yy (gensym 'y))
   (redex-match L
     (bd x x_body) `(bd ,yy ,yy)))

 (define (binding:freshen-match)
   (redex-match binding:L
     (bd x x_body) `(bd y y)))

 (define (binding:freshen-skip-internal-match)
   (redex-match binding:L
     (bd x x_body) bd-v-w-s))

 (perf-test (noop-match manual:freshen-match binding:freshen-match binding:freshen-skip-internal-match)
            `() 25000)

 (define (redex-equal? lhs rhs)
   (redex-match L (any any) (term (,lhs ,rhs))))

 (define (binding:redex-equal? lhs rhs)
   (redex-match binding:L (any any) (term (,lhs ,rhs))))

 (define (manual:aeq? lhs rhs)
   (match-define `(bd ,lx ,lx_body) lhs)
   (match-define `(bd ,rx ,rx_body) rhs)
   (define new-name (gensym 'x))
   (equal? `(bd ,new-name (if (symbol=? lx_body lx)
                              new-name
                              lx_body))
           `(bd ,new-name (if (symbol=? rx_body rx)
                              new-name
                              rx_body))))

 (define (binding:aeq? lhs rhs)
   (alpha-equivalent? binding:L lhs rhs))

 ;; This function does not work! An internal optimization that assumes that the user doesn't have
 ;; access to `value-with-spec` breaks it. But with that optimization disabled, this runs
 ;; significantly faster than `manual:aeq?`: 222ms instead of 794ms on my machine, for 25000
 ;; iterations.
 #;
 (define (binding:aeq-skip-internal-match? lhs rhs) ;; note that this cheats by ignoring its arguments
   (alpha-equivalent? binding:L bd-v-w-s bd-v-w-s-b-b))

 (perf-test (equal? redex-equal? binding:redex-equal? manual:aeq? binding:aeq?)
            `((bd a a) (bd b b)) 25000)



 )


(module lazy-test racket
 (require redex)
 (require (submod ".." perf-test-tools))
 (require redex/examples/lazy)
 (require (prefix-in binding: redex/examples/lazy-with-binding))

 (define add-5-through-1 (term
                          (let ([Y (λ (f)
                                      (let ([g (λ (x)
                                                  (let ([xx (x x)])
                                                    (f xx)))])
                                        (g g)))]
                                [tri
                                 (λ (me)
                                    (λ (x)
                                       (if0 x
                                            0
                                            (let ([x1 (+ x -1)])
                                              (+ (me x1) x)))))]
                                [five 5])
                            ((Y tri) five))))

 (define 5-noop (term (let ([tri
                             (λ (x)
                                (let ([x1 (+ x -1)])
                                  x))]
                            [five 5])
                        (tri five))))

 (define awkward-add (term
                      (let ([o 1]
                            [t 2]
                            [r 3]
                            [f 4])
                        (((((λ (x)
                               (λ (y)
                                  (λ (z)
                                     (λ (w)
                                        (+ (+ x y)
                                           (+ w z))))))
                            o)
                           t)
                          r)
                         f))))

 (printf "Launchbury's natural semantics for lazy evaluation~n")
 (perf-test (run binding:run) (list add-5-through-1) 20)

 (perf-test (run binding:run) (list 5-noop) 5000)

 (perf-test (run binding:run) (list awkward-add) 5000)

 (define (do-subst in old new)
   (term (subst ,in ,old ,new)))
 (define (binding:do-subst in old new)
   (parameterize [(default-language binding:L)] (term (substitute ,in ,old ,new))))

 (define-metafunction binding:L
   binding:mf-subst : any x y -> any
   [(binding:mf-subst x x y) y]
   [(binding:mf-subst (any ...) x y)
    ((binding:mf-subst any x y) ...)]
   [(binding:mf-subst any x y)
    any])

 (define (binding:do-subst-mf in old new)
   (term (binding:mf-subst ,in ,old ,new)))

 (define complex-repetitious-term
   (term (let ([x (λ (x) (x x))]
               [y ((λ (x) (x x))
                   x)]
               [z ((λ (x) (x x))
                   x)])
           (+ (+ (+ (λ (x) (x x))
                    (λ (x) (x x)))
                 (+ (λ (x) (x x))
                    (λ (x) (x x))))
              (+ (+ (λ (x) (x x))
                    (λ (x) (x x)))
                 (+ (λ (x) (x x))
                    (λ (x) (x x))))))))


 (perf-test (do-subst binding:do-subst binding:do-subst-mf) `((λ (x) ((λ (y) x) y)) y z) 10000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) `((λ (x) ((λ (q) y) y)) y z) 10000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) `((let ([x 1][y 2][z 3]) (+ x y)) x q) 10000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) `(,complex-repetitious-term x y) 500)

)



(module stlc+lists-test racket
  (require redex)
  (require (submod ".." perf-test-tools))
  (require redex/examples/stlc+lists)
  (require (prefix-in binding: redex/examples/stlc+lists-with-binding))

  (define sum-list
    `((λ (x (list int)) ((+ (hd x)) ((+ (hd (tl x))) (hd (tl (tl x))))))
      ((cons 5) ((cons 6) ((cons 7) nil)))))


  (define complex-ho
    `((((((λ (f (int → int))
             (λ (g (int → int))
                (λ (h (int → (int → int)))
                   (λ (x int)
                      (λ (y int)
                         ((h (f (g x))) (g y)))))))
          (λ (x int) ((+ x) 1)))
         (λ (x int) ((+ x) 10)))
        (λ (x int) (λ (y int) ((+ x) ((+ x) ((+ x) y))))))
       1)
      2))

  (printf "STLC, with lists~n")
  (perf-test (Eval binding:Eval) (list sum-list) 200)
  (perf-test (Eval binding:Eval) (list sum-list) 200)
  (perf-test (Eval binding:Eval) (list complex-ho) 100)
  (perf-test (M? binding:M?) (list complex-ho) 25000)
  (perf-test (type-check binding:type-check) (list complex-ho) 5000))

(require 'micro-tests)
(require 'lazy-test)
(require 'stlc+lists-test)

(module+ test
  (module config info (define timeout 200)))
