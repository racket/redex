#lang racket
(require "private/test-util.rkt"
         redex/reduction-semantics)

(module test racket/base)
(reset-count)

(define-language empty-language)

(define-language grammar
  (M (M M)
     number)
  (E hole
     (E M)
     (number E))
  (X (number any)
     (any number))
  (Q (Q ...)
     variable)
  (UN (add1 UN)
      zero))

(define-metafunction grammar
  [(f (side-condition (number_1 number_2)
                      (< (term number_1)
                         (term number_2))))
   x]
  [(f (number 1)) y]
  [(f (number_1 2)) ,(+ (term number_1) 2)]
  [(f (4 4)) q]
  [(f (4 4)) r])

(define-metafunction grammar
  [(g X) x])

(test (term (f (1 17))) 'x)
(test (term (f (11 1))) 'y)
(test (term (f (11 2))) 13)


;; match two clauess => take first one
(test (term (f (4 4))) 'q)

;; match one clause two ways => error
(let ()
  (define-metafunction empty-language
    [(ll (number_1 ... number_2 ...)) (number_1 ...)])
  (test (with-handlers ((exn? (λ (x) 'exn-raised))) 
          (term (ll ()))
          'no-exn)
        'no-exn)
  (test (with-handlers ((exn? (λ (x) 'exn-raised))) 
          (term (ll (4 4)))
          'no-exn)
        'exn-raised))

;; match no ways => error
(test (with-handlers ((exn? (λ (x) 'exn-raised))) (term (f mis-match)) 'no-exn)
      'exn-raised)

;; test redex-match in RHS and side-condition
(let ()
  (define-metafunction empty-language
    [(f)
     ,(and (redex-match empty-language number 7) #t)
     (side-condition (redex-match empty-language number 7))])
  (test (term (f)) #t))

(define-metafunction grammar
  [(h (M_1 M_2)) ((h M_2) (h M_1))]
  [(h number_1) ,(+ (term number_1) 1)])

(test (term (h ((1 2) 3)))
      (term (4 (3 2))))

(define-metafunction grammar
  [(h2 (Q_1 ...)) ((h2 Q_1) ...)]
  [(h2 variable) z])

(test (term (h2 ((x y) a b c)))
      (term ((z z) z z z)))

(let ()
  (define-metafunction empty-language
    [(f (1)) 1]
    [(f (2)) 2]
    [(f 3) 3])
  (test (in-domain? (f 1)) #f)
  (test (in-domain? (f (1))) #t)
  (test (in-domain? (f ((1)))) #f)
  (test (in-domain? (f 3)) #t)
  (test (in-domain? (f 4)) #f))

(let ()
  (define-metafunction empty-language
    f : number -> number
    [(f 1) 1])
  (test (in-domain? (f 1)) #t)
  (test (in-domain? (f 2)) #t)
  (test (in-domain? (f x)) #f))

(let ()
  (define-metafunction empty-language
    [(f x) x])
  (test 
   (term-let ((y 'x))
             (in-domain? (f y)))
   #t)
  (test 
   (term-let ((y 'z))
             (in-domain? (f y)))
   #f))

(let ()
  (define-language foo)
  
  (test (term-let ([bar 23])
                  (term 5 #:lang foo))
        5)
  
  (test (term-let ([foo 23])
                  (term 6 #:lang foo))
        6)
  
  (test (term-let ([foo 12])
                  (term-let ([foo 23])
                            (term 7 #:lang foo)))
        7)
  )

; Extension reinterprets the base meta-function's contract
; according to the new language.
(let ()
  (define-language L (x 1))
  (define-extended-language M L (x 2))
  (define-metafunction L
    f : x -> x
    [(f x) x])
  (define-metafunction/extension f M
    [(g q) q])
  
  (with-handlers ([(λ (x) 
                     (and (exn:fail? x)
                          (regexp-match? #rx"no clauses matched"
                                         (exn-message x))))
                   (λ (_) #f)])
    (test (begin (term (g 2)) #t) #t))
  
  (test (in-domain? (g 2)) #t))

; in-domain? interprets base meta-function LHSs according to
; the new language.
(let ()
  (define-language L (x 1))
  (define-extended-language M L (x 2))
  (define-metafunction L
    [(f x) x])
  (define-metafunction/extension f M
    [(g q) q])
  (test (in-domain? (g 2)) #t))

;; mutually recursive metafunctions
(define-metafunction grammar
  [(odd zero) #f]
  [(odd (add1 UN_1)) (even UN_1)])

(define-metafunction grammar
  [(even zero) #t]
  [(even (add1 UN_1)) (odd UN_1)])

(test (term (odd (add1 (add1 (add1 (add1 zero))))))
      (term #f))

(let ()
  (define-metafunction empty-language
    [(pRe xxx) 1])
  
  (define-metafunction empty-language
    [(Merge-Exns any_1) any_1])
  
  (test (term (pRe (Merge-Exns xxx)))
        1))

(let ()
  (define-metafunction empty-language
    [(f (x)) ,(term-let ([var-should-be-lookedup 'y]) (term (f var-should-be-lookedup)))]
    [(f y) y]
    [(f var-should-be-lookedup) var-should-be-lookedup]) ;; taking this case is bad!
  
  (test (term (f (x))) (term y)))

(let ()
  (define-metafunction empty-language
    [(f (x)) (x ,@(term-let ([var-should-be-lookedup 'y]) (term (f var-should-be-lookedup))) x)]
    [(f y) (y)]
    [(f var-should-be-lookedup) (var-should-be-lookedup)]) ;; taking this case is bad!
  
  (test (term (f (x))) (term (x y x))))

(let ()
  (define-metafunction empty-language
    [(f (any_1 any_2))
     case1
     (side-condition (not (equal? (term any_1) (term any_2))))
     (side-condition (not (equal? (term any_1) 'x)))]
    [(f (any_1 any_2))
     case2
     (side-condition (not (equal? (term any_1) (term any_2))))]
    [(f (any_1 any_2))
     case3])
  (test (term (f (q r))) (term case1))
  (test (term (f (x y))) (term case2))
  (test (term (f (x x))) (term case3)))

(let ()
  (define-metafunction empty-language
    [(f (n number)) (n number)]
    [(f (a any)) (a any)]
    [(f (v variable)) (v variable)]
    [(f (s string)) (s string)])
  (test (term (f (n 1))) (term (n 1)))
  (test (term (f (a (#f "x" whatever)))) (term (a (#f "x" whatever))))
  (test (term (f (v x))) (term (v x)))
  (test (term (f (s "x"))) (term (s "x"))))

;; test ..._1 patterns
(let ()
  (define-metafunction empty-language
    [(zip ((variable_id ..._1) (number_val ..._1)))
     ((variable_id number_val) ...)])
  
  (test (term (zip ((a b) (1 2)))) (term ((a 1) (b 2)))))

(let ()
  (define-metafunction empty-language
    [(f any_1 any_2 any_3) (any_3 any_2 any_1)])
  (test (term (f 1 2 3)) 
        (term (3 2 1))))

(let ()
  (define-metafunction empty-language
    [(f (any_1 any_2 any_3)) 3])
  (define-metafunction/extension f empty-language
    [(g (any_1 any_2)) 2])
  (define-metafunction/extension g empty-language
    [(h (any_1)) 1])
  (test (term (h (1))) 1)
  (test (term (h (1 2))) 2)
  (test (term (h (1 2 3))) 3))

(let ()
  (define-metafunction empty-language
    [(f any_1 any_2 any_3) 3])
  (define-metafunction/extension f empty-language
    [(g any_1 any_2) 2])
  (define-metafunction/extension g empty-language
    [(h any_1) 1])
  (test (term (h 1)) 1)
  (test (term (h 1 2)) 2)
  (test (term (h 1 2 3)) 3))

(let ()
  (define-metafunction empty-language
    [(f number_1 number_2) (f number_1)])
  (define-metafunction/extension f empty-language
    [(g number_1) number_1])
  (define-metafunction empty-language
    [(h number_1 number_2) (h number_1)]
    [(h number_1) number_1])
  (test (term (g 11 17)) 11)
  (test (term (h 11 17)) 11))

(let ()
  (define-language L 
    (v 1))
  (define-extended-language M
    L
    (v .... 2))
  (define-metafunction L
    [(f v) v])
  (define-metafunction/extension f M
    [(g 17) 17])
  (test (term (g 2)) 2))

(let ()
  (define-metafunction empty-language
    [(f any) 1])
  (define-metafunction/extension f empty-language
    [(g any) 2])
  (test (term (g 0)) 2))

(let ()
  (define-language L 
    (v 1 (v)))
  (define-metafunction L
    f : v -> v
    [(f (v)) 
     any_1
     (where any_1 (f v))])
  
  (define-extended-language M
    L
    (v .... 2))
  (define-metafunction/extension f M
    g : v -> v
    [(g 2) 2])
  
  (test (term (g (2))) 2))

(let ()
  (define-language L (x 1))
  (define-extended-language M L (x 2))
  (define-metafunction L 
    [(f)
     yes
     (where x 2)]
    [(f)
     no])
  (define-metafunction/extension f M
    g : -> any)
  (test (term (g)) 'yes))

(let ()
  (define-metafunction empty-language
    [(f (number_1 number_2))
     number_3
     (where number_3 ,(+ (term number_1) (term number_2)))])
  (test (term (f (11 17))) 28))

(let ()
  (define-metafunction empty-language
    [(f variable) 
     (any_x any_x)
     (where any_x (variable variable))])
  (test (term (f z)) 
        (term ((z z) (z z)))))

(let ()
  (define-metafunction empty-language
    [(f number_1)
     number_1
     (where number_2 ,(add1 (term number_1)))
     (where number_3 ,(add1 (term number_2)))
     (side-condition (and (number? (term number_3))
                          (= (term number_3) 4)))]
    [(f any) 0])
  (test (term (f 2)) 2))

(let ()
  (define-language x-lang
    (x variable))
  (define-metafunction x-lang
    f : x x -> x
    [(f x_1 x_2) x_1])
  (test (term (f p q)) (term p))
  (test (in-domain? (f p q)) #t))

(let ()
  (define-metafunction empty-language
    [(err number_1 ... number_2 ...) (number_1 ...)])
  (test (term (err)) (term ()))
  (test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                        ((λ (x) #t) (λ (x) 'wrong-exn)))
          (term (err 1 2))
          'no-exn)
        'right-exn))

(let ()
  (define-metafunction empty-language
    err : number ... -> number
    [(err number ...) 1])
  (test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                        ((λ (x) #t) (λ (x) 'wrong-exn)))
          (term (err #f #t))
          'no-exn)
        'right-exn))

(let ()
  (define-metafunction empty-language
    err : number ... -> number
    [(err number ...) #f])
  (test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                        ((λ (x) #t) (λ (x) 'wrong-exn)))
          (term (err 1 2))
          'no-exn)
        'right-exn))

(let ()
  (define-metafunction empty-language
    err : number ... -> (number number)
    [(err number ...) (number ...)])
  (test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                        ((λ (x) #t) (λ (x) 'wrong-exn)))
          (term (err 1 2))
          'no-exn)
        'no-exn)
  (test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                        ((λ (x) #t) (λ (x) 'wrong-exn)))
          (term (err 1 1))
          'no-exn)
        'no-exn))

(let ()
  ;; test that 'where' clauses can contain recursive calls.
  (define-metafunction empty-language
    [(f (any)) 
     x
     (where x (f any))]
    [(f any) any])
  (test (term (f ((((x))))))
        (term x)))

(let ()
  (define-language lamv
    (z (variable hole) hole))
  
  (define-metafunction lamv
    foo : z  -> any
    [(foo hole) dontcare]
    [(foo (variable hole)) docare])
  
  (test (term (foo hole))
        (term dontcare))
  (test (term (foo (y hole)))
        (term docare)))

(let ()
  (define f-called? #f)
  (define-metafunction empty-language
    f : (side-condition any_1 (begin (set! f-called? #t) #t)) -> any
    [(f any_1) any_1])
  (test (term (f 1)) 1)
  (test f-called? #t))

(let ()
  (define g-called? #f)
  (define-metafunction empty-language
    g : any -> (side-condition any_1 (begin (set! g-called? #t) #t))
    [(g any_1) any_1])
  (test (term (g 1)) 1)
  (test g-called? #t))

;; test that tracing works properly
;; note that caching comes into play here (which is why we don't see the recursive calls)
(let ()
  (define-metafunction empty-language
    [(f 0) 0]
    [(f number) (f ,(- (term number) 1))])
  
  (let ([sp (open-output-string)])
    (parameterize ([current-output-port sp])
      (term (f 1)))
    (test (get-output-string sp) ""))
  
  (let ([sp (open-output-string)])
    (parameterize ([current-output-port sp]
                   [current-traced-metafunctions 'all]
                   [print-as-expression #f])
      (term (f 1)))
    (test (get-output-string sp) "c>(f 1)\n <0\n"))
  
  (let ([sp (open-output-string)])
    (parameterize ([current-output-port sp]
                   [current-traced-metafunctions 'all]
                   [print-as-expression #f]
                   [caching-enabled? #f])
      (term (f 1)))
    (test (get-output-string sp) " >(f 1)\n > (f 0)\n < 0\n <0\n"))
  
  (let ([sp (open-output-string)])
    (parameterize ([current-output-port sp]
                   [current-traced-metafunctions '(f)]
                   [print-as-expression #f])
      (term (f 1)))
    (test (get-output-string sp) "c>(f 1)\n <0\n"))
  
  
  (define-metafunction empty-language
    [(g (any)) ((g any) (g any))]
    [(g 1) 1])
  
  (let ([sp (open-output-string)])
    (parameterize ([current-output-port sp]
                   [current-traced-metafunctions '(g)]
                   [print-as-expression #f])
      (term (g (1))))
    (test (get-output-string sp) " >(g (1))\n > (g 1)\n < 1\nc> (g 1)\n < 1\n <(1 1)\n"))
  
  )

(let ()
  (define-language var-lang [(x y z w) variable])
  
  ;; this should produce the second case, 
  ;; since the where clause (should) fail to match 
  ;; in the first case.
  (define-metafunction var-lang
    [(f x)
     first-case
     (where (AnotherAtom y) (Atom x))]
    [(f x)
     second-case])
  
  (test (term (f a)) (term second-case)))

(let ()
  
  ;; this is an ambiguous function 
  ;; and should signal an error if it is ever called
  ;; with multiple different arguments, but if the
  ;; arguments are all the same, it will return
  ;; the same result for any parse, and thus should be allowed.
  (define-metafunction empty-language
    [(f any_x ... any_y any_z ...)
     any_y])
  
  (test (term (f 1 1 1 1 1)) (term 1)))

(let ()
  (define-metafunction empty-language
    [(ex variable_x) 
     variable_x
     (where quote variable_x)])
  
  (test (term (ex quote)) (term quote)))

(let ()
  (define-metafunction empty-language
    [(f any ...)
     (any ...)
     (where variable_1 x)
     (side-condition #f)
     (where (number ...) y)]
    [(f any ...)
     12345])
  
  (test (term (f 8)) 12345))

(let ()
  (define-metafunction empty-language
    [(f number_1 number_2 ... (number_s ...) ...)
     yes
     (where number_1 1)
     (where (number_3 ...) ,(cdr (term (number_2 ...))))
     (where (number_3 ...) (3 4 5))
     (where (number_1 (number_s ...) ...)
            ,(if (null? (term ((number_s ...) ...)))
                 (term (number_1))
                 (term (number_1 () (6) (7 8) (9 10 11)))))]
    [(f any ...)
     no])
  (test (term (f 1 2 3 4 5)) 'yes)
  (test (term (f 1 2 3 4)) 'no)
  (test (term (f 0 2 3 4 5)) 'no)
  (test (term (f 1 2 3 4 5 () (6) (7 8) (9 10 11))) 'yes))

(let ()
  (define-language L 
    [bool #t #f])
  (define-metafunction L
    f : any -> bool or number
    [(f any) any])
  (test (term (f 1)) (term 1))
  (test (term (f #f)) (term #f)))

(let ()
  (define-language L 
    [bool #t #f])
  (define-metafunction L
    f : any -> bool ∪ number
    [(f any) any])
  (test (term (f 1)) (term 1))
  (test (term (f #f)) (term #f)))

(let ()
  (define-language L 
    [bool #t #f]
    [abc a b c]
    [def d e f])
  (define-metafunction L
    f : any -> bool ∨ number ∪ abc or def
    [(f any) any])
  (test (term (f 1)) (term 1))
  (test (term (f #f)) (term #f))
  (test (term (f c)) (term c))
  (test (term (f e)) (term e)))

;; test that the contracts are called in order (or else 'car' fails)
(let ()
  (define x '())
  (define-language L
    [seq (any any ...)])
  (define-metafunction L
    g : any -> 
    (side-condition any_1 (begin (set! x (cons 1 x)) #f))
    or (side-condition any_1 (begin (set! x (cons 2 x)) #f))
    or any
    [(g any) any])
  (test (begin (term (g whatever))
               x)
        '(2 1)))

(let ()
  
  (define-metafunction empty-language
    must-be-identity : natural_1 -> natural_1
    [(must-be-identity any) 0])
  
  (test (with-handlers ((exn:fail:redex? exn-message))
          (term (must-be-identity 1)))
        #rx"codomain test failed")
  
  (define-metafunction empty-language
    [(same any_1 any_1) #t]
    [(same any_1 any_2) #f])
  
  (define-metafunction empty-language
    m : any_1 any_2 -> any_3
    #:pre (same any_1 any_2)
    [(m any_x any_y) any_x])
  
  (test (term (m 1 1)) 1)
  (test (with-handlers ((exn:fail:redex? exn-message))
          (term (m 1 2)))
        #rx"is not in my domain")
  
  (define-metafunction empty-language
    is-nat : any -> boolean
    [(is-nat natural) #t]
    [(is-nat any) #f])
  
  (define-metafunction empty-language
    post-only : any_1 -> any_2
    #:post (same any_1 any_2)
    [(post-only any) 1])
  
  (test (term (post-only 1)) 1)
  (test (with-handlers ([exn:fail:redex? exn-message])
          (term (post-only 2)))
        #rx"codomain")
  
  (define-metafunction empty-language
    pre-and-post : any_1 -> any_2
    #:pre (is-nat any_1)
    #:post (same any_1 any_2)
    [(pre-and-post any) 1])
  
  (test (term (pre-and-post 1)) 1)
  (test (with-handlers ([exn:fail:redex? exn-message])
          (term (pre-and-post x)))
        #rx"is not in my domain")
  (test (with-handlers ([exn:fail:redex? exn-message])
          (term (pre-and-post 2)))
        #rx"codomain")
  )

(let ()
  (define-language L
    (n z (s n)))
  
  (define-metafunction L
    [(f n)
     n_1
     (judgment-holds (p n n_1))])
  
  (define-judgment-form L
    #:mode (p I O)
    #:contract (p n n)
    [(p z z)]
    [(p (s n) n)]
    [(p (s n) z)])
  
  (test (term (f (s z)))
        (term z))
  (test (with-handlers ([exn:fail:redex? exn-message])
          (term (f (s (s z))))
          "")
        #rx"returned different results"))

;; errors for not-yet-defined metafunctions
(test (let ([on (current-namespace)])
        (parameterize ([current-namespace (make-base-namespace)])
          (namespace-attach-module on 'redex/reduction-semantics)
          (namespace-require 'racket/base)
          (eval '(module m racket
                   (require redex/reduction-semantics)
                   (term (q))
                   (define-language L)
                   (define-metafunction L [(q) ()])))
          (with-handlers ([exn:fail:contract:variable? exn-message])
            (eval '(require 'm))
            #f)))
      #rx"^q: undefined;\n[^\n]*use[^\n]*before")
(test (with-handlers ([exn:fail:contract:variable? exn-message])
        (let ()
          (term (q))
          (define-language L)
          (define-metafunction L [(q) ()])
          #f))
      #rx"^q: undefined;\n[^\n]*use[^\n]*before")
(test (let ([on (current-namespace)])
        (parameterize ([current-namespace (make-base-namespace)])
          (namespace-attach-module on 'redex/reduction-semantics)
          (namespace-require 'racket/base)
          (with-handlers ([exn:fail? exn-message])
            (eval '(module m racket
                     (require redex/reduction-semantics)
                     (define-metafunction)))
            "no exn raised")))
      #rx"define-metafunction: expected the name of a language")

(let ()
  ;; named ellipses in where clauses
  (define-language L)
  
  (define-metafunction L
    [(f (any ..._n))
     3
     (where (any_2 ..._n) (1 2 3))]
    [(f any)
     #f])
  
  (test (term (f (a b c))) 3)
  (test (term (f (a b))) #f))

(let ()
  ;; 'or' in metafunctions
  (define-language L)
  
  (define-metafunction L
    [(f any ...)
     three
     (where (any_1 any_2 any_3) (any ...))
     or
     two
     (where (any_1 any_2) (any ...))
     or
     something-else])
  
  (test (term (f a b c)) (term three))
  (test (term (f a b)) (term two))
  (test (term (f a)) (term something-else)))


(let ()
  (define-language lc-lang
    (e (e e ...)
       x
       v)
    (c (v ... c e ...)
       hole)
    (v (lambda (x ...) e))
    (x variable-not-otherwise-mentioned))
  
  (test (let ([m (redex-match lc-lang e (term (lambda (x) x)))])
          (and m (length m)))
        1)
  
  (define-extended-language qabc-lang lc-lang (q a b x))
  
  (test (redex-match qabc-lang
                     e
                     (term (lambda (a) a)))
        #f)
  
  (test (let ([m (redex-match qabc-lang
                              e
                              (term (lambda (z) z)))])
          (and m (length m)))
        1)
  
  (define-metafunction lc-lang
    free-vars : e -> (x ...)
    [(free-vars (e_1 e_2 ...))
     (∪ (free-vars e_1) (free-vars e_2) ...)]
    [(free-vars x) (x)]
    [(free-vars (lambda (x ...) e))
     (- (free-vars e) (x ...))])
  
  (define-metafunction lc-lang
    ∪ : (x ...) ... -> (x ...)
    [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
     (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
    [(∪ (x_1 ...))
     (x_1 ...)]
    [(∪) ()])
  
  (define-metafunction lc-lang
    - : (x ...) (x ...) -> (x ...)
    [(- (x ...) ()) (x ...)]
    [(- (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
     (- (x_1 ... x_3 ...) (x_2 x_4 ...))
     (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
    [(- (x_1 ...) (x_2 x_3 ...))
     (- (x_1 ...) (x_3 ...))])
  
  (test (term (∪)) (term ()))
  (test (term (∪ (x y) (z a) (b c))) (term (x y z a b c)))
  
  (test (term (- (x y) ())) (term (x y)))
  (test (term (- (x y) (x))) (term (y)))
  (test (term (- (y x) (x))) (term (y)))
  (test (term (- (x x x x x) (x))) (term ()))
  
  (test (term (free-vars (lambda (x) (x y)))) (list 'y))
  (test (term (free-vars (a (b (c (d e)))))) (term (a b c d e))))

(print-tests-passed 'tl-metafunctions.rkt)
