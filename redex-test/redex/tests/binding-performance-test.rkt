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

     (printf "~a:~n" 't)

     (begin
       (printf "  ~a:~n" (symbol->string 'runner))
       (printf "    ")
       (collect-garbage) (collect-garbage) (collect-garbage)
       (time (times repeat-count (apply runner t)))) ...)))


(module micro-tests racket
 (require redex)
 (require redex/private/binding-forms-compiler)
 (require redex/private/binding-forms-definitions)
 (require (submod ".." perf-test-tools))


 (define-syntax (bspec-of stx)
   (syntax-case stx ()
     [(form-name (all-nts ...) . bf-forms)
      #`(second (first #,(compile-binding-forms #`bf-forms
                                                (syntax->datum #`(all-nts ...))
                                                #`form-name)))]))


 (printf "Microbenchmarks~n")

 (define-language L
   (e (bd x x)
      (complex-bd ((x x) ...) ... x))
   (x variable-not-otherwise-mentioned))

 (define-language binding:L
   (e (bd x x)
      (complex-bd ((x x) ...) ... x))
   (x variable-not-otherwise-mentioned)
   #:binding-forms
   (bd x x_body #:refers-to x)
   (complex-bd ((x_0 x_v #:refers-to x_0) ...) ... x_body #:refers-to (shadow (shadow x_0 ...) ...)))


 ;; special values for `bd`
 (define bd-bspec (bspec-of (x e) (bd x x_body #:refers-to x)))
 (define bd-v-w-s
   (value-with-spec
    (match-bindings (first (redex-match L (bd x x_body) `(bd a a))))
    bd-bspec))
 (define bd-v-w-s-b-b
   (value-with-spec
    (match-bindings (first (redex-match L (bd x x_body) `(bd b b))))
    bd-bspec))






 ;; special values for `complex-bd`
 (define complex-bd-bspec
   (bspec-of (x e)
             (complex-bd ((x_0 x_v #:refers-to x_0) ...) ...
                         x_body #:refers-to (shadow (shadow x_0 ...) ...))))
 (define cbd-v
   `(complex-bd ((a a) (b f1) (c c)) ((d f2)) c))

 (define cbd-v-renamed
   `(complex-bd ((aa aa) (bb f1) (cc cc)) ((dd f2)) cc))

 (define cbd-v-w-s
   (value-with-spec
    (match-bindings (first (redex-match L (complex-bd ((x_0 x_v) ...) ... x_body)
                                        cbd-v)))
    complex-bd-bspec))
 (define cbd-v-w-s-renamed
   (value-with-spec
    (match-bindings (first (redex-match L (complex-bd ((x_0 x_v) ...) ... x_body)
                                        cbd-v-renamed)))
    complex-bd-bspec))


 ;; matches

 (define (noop-match v)
   (redex-match L
     (any ...) v))

 (define (manual:freshen-match v)
   (redex-match L
     (any ...)
     (cond
      [(symbol=? (first v) 'bd)
       (define yy (gensym 'y))
       `(bd ,yy ,(if (symbol=? (second v) (third v))
                     yy
                     (third v)))]
      [else
       (match-define `(complex-bd ((,x ,x-v) ...) ... ,x-body) v)
       (define fresh-x (map (λ (x) (map gensym x)) x))

       `(complex-bd
         ;; each clause is simple to reconstruct
         ,@(map (λ (x fresh-x x-v)
                   (map (λ (x fresh-x x-v)
                           `(,fresh-x ,(if (symbol=? x-v x) fresh-x x-v)))
                        x fresh-x x-v))
                x fresh-x x-v)
         (match
          (assq
           x-body
           (map ;; create a lookup table of in-scope names
            (λ (x fresh-x) `(,x ,fresh-x))
            (append* x) (append* fresh-x))) ;; flatten everything
          [#f x-body]
          [`(,_ ,fresh-x) fresh-x]))])))

 (define (binding:freshen-match v)
   (redex-match binding:L
     (any ...) v))

 (define (binding:freshen-skip-internal-match v)
   (redex-match binding:L
     (any ...)
     (if (symbol=? (first v) 'bd)
         bd-v-w-s
         cbd-v-w-s)))




 (perf-test (noop-match manual:freshen-match binding:freshen-match binding:freshen-skip-internal-match)
            `((bd y y)) 25000)

 (perf-test (noop-match manual:freshen-match binding:freshen-match binding:freshen-skip-internal-match)
            `(,cbd-v) 25000)


 ;; alpha-equivalence tests

 (define (redex-equal? lhs rhs)
   (redex-match L (any any) (term (,lhs ,rhs))))

 (define (binding:redex-equal? lhs rhs)
   (redex-match binding:L (any any) (term (,lhs ,rhs))))

 (define (manual:aeq? lhs rhs)
   (cond
    [(symbol=? (first lhs) 'bd)

     (match-define `(bd ,lx ,lx_body) lhs)
     (match-define `(bd ,rx ,rx_body) rhs)
     (define new-name (gensym 'x))
     (equal? `(bd ,new-name ,(if (symbol=? lx_body lx)
                                 new-name
                                 lx_body))
             `(bd ,new-name ,(if (symbol=? rx_body rx)
                                 new-name
                                 rx_body)))]
    [else
     (match-define `(complex-bd ((,l-x ,l-x-v) ...) ... ,l-x-body) lhs)
     (match-define `(complex-bd ((,r-x ,r-x-v) ...) ... ,r-x-body) rhs)

     (define flat-l-x (append* l-x))
     (define flat-r-x (append* r-x))
     (define flat-l-x-v (append* l-x-v))
     (define flat-r-x-v (append* r-x-v))


     (and
      (andmap
       (lambda (l-x l-x-v r-x r-x-v)
         (or (symbol=? l-x-v r-x-v)
             (and (symbol=? l-x l-x-v)
                  (symbol=? r-x r-x-v))))
       flat-l-x flat-l-x-v flat-r-x flat-r-x-v)
      (or (symbol=? l-x-body r-x-body)
          (ormap (lambda (l-x r-x)
                   (and (symbol=? l-x-body l-x)
                        (symbol=? r-x-body r-x)))
                 flat-l-x
                 flat-r-x)))]))


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

 (perf-test (equal? redex-equal? binding:redex-equal? manual:aeq? binding:aeq?)
            `(,cbd-v ,cbd-v-renamed) 25000)



 )


(module lazy-test racket
 (require redex)
 (require (submod ".." perf-test-tools))
 (require redex/examples/lazy)
 (require (prefix-in binding: redex/examples/lazy-with-binding))

 ;; to avoid metafunction caching, we generate variables fresh each time

 (define (add-5-through-1)
   ;; the goal is to have almost every subterm contain a generated name
   (define x (gensym)) (define g (gensym)) (define tri (gensym)) (define me (gensym))
   (define f (gensym))
   `(let ([Y (λ (,f)
                (let ([,g (λ (,x)
                            (let ([xx (,x ,x)])
                              (,f xx)))])
                  (,g ,g)))]
          [,tri
           (λ (,me)
              (λ (,x)
                 (if0 ,x
                      0
                      (let ([x1 (+ ,x -1)])
                        (+ (,me x1) ,x)))))]
          [five 5])
      ((Y ,tri) five)))

 (define (5-noop)
   (define five (gensym))
   (define x (gensym))
   `(let ([tri
           (λ (,x)
              (let ([x1 (+ ,x -1)])
                ,x))]
          [,five 5])
      (tri ,five)))

 (define (awkward-add)
   (define z (gensym))
   (define x (gensym))
   (define f (gensym))
   `(let ([o 1]
          [t 2]
          [r 3]
          [,f 4])
      (((((λ (,x)
             (λ (y)
                (λ (,z)
                   (λ (w)
                      (+ (+ ,x y)
                         (+ w ,z))))))
          o)
         t)
        r)
       ,f)))

 (printf "Launchbury's natural semantics for lazy evaluation~n")
 (perf-test (run binding:run) (list (add-5-through-1)) 20)

 (perf-test (run binding:run) (list (5-noop)) 1000)

 (perf-test (run binding:run) (list (awkward-add)) 500)

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

 (define (simple-term-1)
   (define x (gensym)) (define y (gensym))
   `((λ (,x) ((λ (,y) ,x) ,y)) ,y z))

 (define (simple-term-2)
   (define x (gensym)) (define y (gensym))
   `((λ (,x) ((λ (q) ,y) ,y)) ,y z))

 (define (term-with-let)
   (define x (gensym)) (define y (gensym)) (define z (gensym))
   `((let ([,x 1][,y 2][,z 3]) (+ ,x ,y)) ,x q))

 (define (complex-repetitious-term)
   (define x (gensym))
   `((let ([,x (λ (,x) (,x ,x))]
                [y ((λ (,x) (,x ,x))
                    ,x)]
                [z ((λ (,x) (,x ,x))
                    ,x)])
            (+ (+ (+ (λ (,x) (,x ,x))
                     (λ (,x) (,x ,x)))
                  (+ (λ (,x) (,x ,x))
                     (λ (,x) (,x ,x))))
               (+ (+ (λ (,x) (,x ,x))
                     (λ (,x) (,x ,x)))
                  (+ (λ (,x) (,x ,x))
                     (λ (,x) (,x ,x))))))
          ,x
          y))


 (perf-test (do-subst binding:do-subst binding:do-subst-mf) (simple-term-1) 5000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) (simple-term-2) 5000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) (term-with-let) 3000)

 (perf-test (do-subst binding:do-subst binding:do-subst-mf) (complex-repetitious-term) 500)

)



(module stlc+lists-test racket
  (require redex)
  (require (submod ".." perf-test-tools))
  (require redex/examples/stlc+lists)
  (require (prefix-in binding: redex/examples/stlc+lists-with-binding))

  (define (sum-list)
    (define x (gensym))
    `((λ (,x (list int)) ((+ (hd ,x)) ((+ (hd (tl ,x))) (hd (tl (tl ,x))))))
      ((cons 5) ((cons 6) ((cons 7) nil)))))


  (define (complex-ho)
    (define x (gensym))
    (define y (gensym))
    `((((((λ (f (int → int))
             (λ (g (int → int))
                (λ (h (int → (int → int)))
                   (λ (,x int)
                      (λ (,y int)
                         ((h (f (g ,x))) (g ,y)))))))
          (λ (,x int) ((+ ,x) 1)))
         (λ (,x int) ((+ ,x) 10)))
        (λ (,x int) (λ (,y int) ((+ ,x) ((+ ,x) ((+ ,x) ,y))))))
       1)
      2))

  (printf "STLC, with lists~n")
  (perf-test (Eval binding:Eval) (list (sum-list)) 200)
  (perf-test (Eval binding:Eval) (list (sum-list)) 200)
  (perf-test (Eval binding:Eval) (list (complex-ho)) 100)
  (perf-test (M? binding:M?) (list (complex-ho)) 25000)
  (perf-test (type-check binding:type-check) (list (complex-ho)) 5000))

(require 'micro-tests)
(require 'lazy-test)
(require 'stlc+lists-test)
