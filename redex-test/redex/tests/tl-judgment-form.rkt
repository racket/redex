#lang racket
(require "private/test-util.rkt"
         redex/reduction-semantics
         racket/match
         racket/trace)

(module test racket/base)
(reset-count)

(define-language empty-language)

(let ()
  (define-language nats
    (n z (s n)))
  
  (define-judgment-form nats
    #:mode (sumi I I O)
    #:contract (sumi n n n)
    [(sumi z n n)]
    [(sumi (s n_1) n_2 (s n_3))
     (sumi n_1 n_2 n_3)])
  (test (judgment-holds (sumi z (s z) n) n)
        (list (term (s z))))
  (test (judgment-holds (sumi (s (s z)) (s z) n) n)
        (list (term (s (s (s z))))))
  (test (judgment-holds (sumi ,'z (s z) (s z))) #t)
  
  (define-judgment-form nats
    #:mode (sumi2 I I O)
    #:contract (sumi2 n n n)
    [------------- sumz ;; symbol name
                   (sumi2 z n n)]
    [(sumi2 n_1 n_2 n_3)
     ---------------------------  "sumn" ;; string name
     (sumi2 (s n_1) n_2 (s n_3))])
  (test (judgment-holds (sumi2 z (s z) n) n)
        (list (term (s z))))
  (test (judgment-holds (sumi2 (s (s z)) (s z) n) n)
        (list (term (s (s (s z))))))
  
  (define-judgment-form nats
    #:mode (sumo O O I)
    #:contract (sumo n n n)
    [(sumo z n n)]
    [(sumo (s n_1) n_2 (s n_3))
     (sumo n_1 n_2 n_3)])
  (test (judgment-holds (sumo n_1 n_2 z) ([,'n_1 n_1] [,'n_2 n_2]))
        (list (term ([n_1 z] [n_2 z]))))
  (test (judgment-holds (sumo n_1 n_2 (s z)) ([,'n_1 n_1] [,'n_2 n_2]))
        (list (term ([n_1 (s z)] [n_2 z]))
              (term ([n_1 z] [n_2 (s z)]))))
  
  (define-judgment-form nats
    #:mode (sumo-ls O O I)
    [(sumo-ls (s n_1) n_2 n_3)
     (sumo (s n_1) n_2 n_3)])
  (test (judgment-holds (sumo-ls n_1 n_2 (s z)) ([,'n_1 n_1] [,'n_2 n_2]))
        (list (term ([n_1 (s z)] [n_2 z]))))
  (test (judgment-holds (sumo-ls (s n_1) n_2 (s z))) #t)
  (test (judgment-holds (sumo-ls z n_2 (s z))) #f)
  (test (judgment-holds (sumo-ls z n_2 (s z)) whatever) (list))
  
  (define-judgment-form nats
    #:mode (sumo-lz O O I)
    [(sumo-lz z n_2 n_3)
     (sumo z n_2 n_3)])
  (test (judgment-holds (sumo-lz n_1 n_2 (s z)) ([,'n_1 n_1] [,'n_2 n_2]))
        (list (term ([n_1 z] [n_2 (s z)]))))
  
  (define-judgment-form nats
    #:mode (member O I)
    [(member n_i (n_0 ... n_i n_i+1 ...))])
  
  (test (judgment-holds (member n (z (s z) z (s (s z)))) n)
        (list (term (s (s z))) (term (s z)) (term z)))
  
  (define-judgment-form nats
    #:mode (has-zero I)
    [(has-zero (n ...))
     (member z (n ...))])
  
  (test (judgment-holds (has-zero ((s z) z (s (s z))))) #t)
  
  (define-judgment-form nats
    #:mode (le2 I)
    [(le2 n)
     (le (add2 n) (s (s (s (s z)))))])
  
  (define-judgment-form nats
    #:mode (le I I)
    [(le z n)]
    [(le (s n_1) (s n_2))
     (le n_1 n_2)])
  
  (define-metafunction nats
    add2 : n -> n
    [(add2 n) (s (s n))])
  
  (test (judgment-holds (le2 (s (s z)))) #t)
  (test (judgment-holds (le2 (s (s (s z))))) #f)
  
  (define-judgment-form nats
    #:mode (uses-add2 I O)
    #:contract (uses-add2 n n)
    [(uses-add2 n_1 n_2)
     (sumo n_2 n_3 n_1)
     (where n_2 (add2 n_3))])
  
  (test (judgment-holds (uses-add2 (s (s (s (s z)))) n) n)
        (list (term (s (s (s z))))))
  
  (define-judgment-form nats
    #:mode (add1 I O)
    #:contract (add1 n n)
    [(add1 n (s n))])
  
  (define-judgment-form nats
    #:mode (map-add1 I O)
    #:contract (map-add1 (n ...) (n ...))
    [(map-add1 (n ...) (n_+ ...))
     (add1 n n_+) ...])
  
  (test (judgment-holds (map-add1 () (n ...))
                        (n ...))
        (list (term ())))
  
  (test (judgment-holds (map-add1 (z (s z) (s (s z))) (n ...))
                        (n ...))
        (list (term ((s z) (s (s z)) (s (s (s z)))))))
  
  (define-judgment-form nats
    #:mode (map-add1-check I O)
    #:contract (map-add1-check (n ...) (n ...))
    [(map-add1-check (n ...) ((s n) ...))
     (add1 n (s n)) ...])
  
  (test (judgment-holds (map-add1-check (z (s z) (s (s z))) (n ...))
                        (n ...))
        (list (term ((s z) (s (s z)) (s (s (s z)))))))
  
  (define-judgment-form nats
    #:mode (add-some-noz I O)
    #:contract (add-some-noz n n)
    [(add-some-noz z z)]
    [(add-some-noz (s n) (s n))]
    [(add-some-noz (s n) (s (s n)))])
  
  (define-judgment-form nats
    #:mode (map-add-some-noz I O)
    #:contract (map-add-some-noz (n ...) (n ...))
    [(map-add-some-noz (n ...) (n_+ ...))
     (add-some-noz n n_+) ...])
  
  (test (sort (judgment-holds (map-add-some-noz (z (s z) (s (s z))) (n ...))
                              (n ...))
              string<=?
              #:key (λ (x) (format "~s" x)))
        (list (term (z (s (s z)) (s (s (s z)))))
              (term (z (s (s z)) (s (s z))))
              (term (z (s z) (s (s (s z)))))
              (term (z (s z) (s (s z))))))
  
  (define-judgment-form nats
    #:mode (add-some I O)
    #:contract (add-some n n)
    [(add-some n n)]
    [(add-some n (s n))])
  
  (define-judgment-form nats
    #:mode (map-add-some-one I O)
    #:contract (map-add-some-one (n ...) (n ...))
    [(map-add-some-one (n ...) ((s n) ...))
     (add-some n (s n)) ...])
  
  (test (judgment-holds (map-add-some-one (z (s z) (s (s z))) (n ...))
                        (n ...))
        (list (term ((s z) (s (s z)) (s (s (s z)))))))
  
  (define-judgment-form nats
    #:mode (hyphens I)
    [(hyphens b)
     -----------
     (hyphens a)]
    [(hyphens c)
     -
     (hyphens b)]
    [(hyphens c)])
  (test (judgment-holds (hyphens a)) #t)
  
  (let-syntax ([test-trace 
                (syntax-rules ()
                  [(_ expr trace-spec expected)
                   (test (let ([trace (open-output-string)])
                           (parameterize ([current-output-port trace]
                                          [current-traced-metafunctions trace-spec])
                             expr)
                           (get-output-string trace))
                         expected)])])
    (test-trace (parameterize ([caching-enabled? #f])
                  (judgment-holds (sumi (s z) (s (s z)) n) n))
                '(sumi)
                #reader scribble/reader
                @string-append{ >(sumi (s z) (s (s z)) _)
                                > (sumi z (s (s z)) _)
                                < ((sumi z (s (s z)) (s (s z))))
                                <((sumi (s z) (s (s z)) (s (s (s z)))))
                                 
                                })
    (test-trace (parameterize ([caching-enabled? #t])
                  (judgment-holds (sumi (s z) (s (s z)) n) n)
                  (judgment-holds (sumi (s z) (s (s z)) n) n))
                '(sumi)
                #reader scribble/reader
                @string-append{ >(sumi (s z) (s (s z)) _)
                                > (sumi z (s (s z)) _)
                                < ((sumi z (s (s z)) (s (s z))))
                                <((sumi (s z) (s (s z)) (s (s (s z)))))
                               c>(sumi (s z) (s (s z)) _)
                                <((sumi (s z) (s (s z)) (s (s (s z)))))
                               
                                })
    (test-trace (parameterize ([caching-enabled? #f])
                  (judgment-holds (sumo n_1 n_2 (s z))))
                'all
                #reader scribble/reader
                @string-append{ >(sumo _ _ (s z))
                                > (sumo _ _ z)
                                < ((sumo z z z))
                                <((sumo (s z) z (s z)) (sumo z (s z) (s z)))
                                
                                })
    
    ;; the leading space in the #t line in the
    ;; trace below is questionable; it probably
    ;; shouldn't be there, but I'm leaving this
    ;; test case as for now
    (test-trace (letrec ([f (match-lambda
                              ['z #t]
                              [`(s ,n) (f n)])])
                  (define-judgment-form nats
                    #:mode (ext-trace I I)
                    [(ext-trace z (side-condition n (f (term n))))]
                    [(ext-trace (s n_1) n_2)
                     (ext-trace n_1 n_2)])
                  (trace f)
                  (parameterize ([caching-enabled? #f])
                    (judgment-holds (ext-trace (s z) (s z)))))
                'all
                #reader scribble/reader
                @string-append{ >(ext-trace (s z) (s z))
                                > (ext-trace z (s z))
                               > >(f '(s z))
                               > >(f 'z)
                                < <#t
                                < ((ext-trace z (s z)))
                                <((ext-trace (s z) (s z)))
                                
                                })))



(let ()
  (define-judgment-form empty-language
    #:mode (R I I)
    [(side-condition (different any_a any_b))
     -----
     (R any_a any_b)])
  (define-metafunction empty-language
    [(different any_a any_a) #f]
    [(different any_a any_b) #t])
  (test (judgment-holds (R 1 2)) #t)
  (test (judgment-holds (R 1 1)) #f)
  (test (term (R 1 2)) #t)
  (test (term (R 1 1)) #f))

(let ()
  (define-judgment-form empty-language
    #:mode (J I O)
    [(J any_2 any_3)
     -----------------
     (J (any_2) any_3)]
    [---------------------
     (J variable variable)])
  
  
  (define-extended-judgment-form empty-language J 
    #:mode (J2 I O)
    
    [------------------
     (J2 number number)]
    
    [(J2 any_1 any_3)
     ------------------------
     (J2 (any_1 any_2) any_3)])
  
  (test (judgment-holds (J (x) any) any) '(x))
  (test (judgment-holds (J2 (1 y) any) any) '(1))
  (test (judgment-holds (J2 (x y) any) any) '(x))
  (test (judgment-holds (J2 ((((x) z) y)) any) any) '(x))
  (test (judgment-holds (J2 ((((11) z) y)) any) any) '(11)))

(let ()
  
  (define-language L1
    (n 1 2 3))
  
  (define-extended-language L2 L1
    (n .... 4 5 6))
  
  (define-judgment-form L1
    #:mode (J1 I O)
    [-----------
     (J1 n_1 n_1)])
  
  (define-extended-judgment-form L2 J1 
    #:mode (J2 I O))
  
  (test (judgment-holds (J1 1 any) any) '(1))
  (test (judgment-holds (J2 1 any) any) '(1))
  (test (judgment-holds (J2 4 any) any) '(4)))

(let ()
  (define-language L (N ::= z (s N) (t N)))
  
  (define-judgment-form L
    #:mode (J2 I O)
    [--------  "one"
               (J2 1 1)]
    [--------  two
               (J2 1 2)])
  
  (test (build-derivations (J2 1 any))
        (list (derivation '(J2 1 1) "one" '())
              (derivation '(J2 1 2) "two" '())))
  
  
  
  (define-judgment-form L
    #:contract (K any any)
    #:mode (K I O)
    [-----------
     (K () z)]
    [(K any_1 N) ...
     ---------------------------
     (K (any_1 ...) (N ...))])
  
  
  
  (test (build-derivations (K (()) any))
        (list (derivation '(K (()) (z))
                          #f
                          (list (derivation '(K () z) #f '())))))
  
  (test
   (build-derivations (K (() ()) any))
   (list (derivation 
          '(K (() ()) (z z))
          #f
          (list
           (derivation '(K () z) #f '())
           (derivation '(K () z) #f '())))))
  
  (define-judgment-form L
    #:contract (J any any)
    #:mode (J I O)
    [--------
     (J () z)]
    [(J any_1 N)  (J any_2 N)
                  ----------------------------
                  (J (any_1 any_2) (s N))]
    [(J any N)
     ---------------
     (J (any) (s N))])
  
  (test (build-derivations 
         (J ((()) (())) N))
        (list (derivation
               '(J ((()) (())) (s (s z)))
               #f
               (list (derivation 
                      '(J (()) (s z))
                      #f
                      (list
                       (derivation
                        '(J () z)
                        #F
                        '())))
                     (derivation 
                      '(J (()) (s z))
                      #f
                      (list
                       (derivation
                        '(J () z)
                        #f
                        '())))))))
  
  (define-judgment-form L
    #:mode (J3 I O)
    [(J any_1 any_2)
     ------------
     (J3 any_1 any_2)])
  
  (test (build-derivations (J3 (()) N))
        (list (derivation
               '(J3 (()) (s z))
               #f
               (list
                (derivation
                 '(J (()) (s z))
                 #f
                 (list 
                  (derivation 
                   '(J () z)
                   #f
                   '()))))))))

(let ()
  (define-judgment-form empty-language #:mode (J I) [(J any)])
  ;; test that the judgment form cache doesn't interfere with build-derivations
  (define term 'x)
  (test (judgment-holds (J ,term)) #t)
  (test (build-derivations (J ,term))
        (list (derivation '(J x) #f '())))
  (test (IO-judgment-form? J) #f))

(let ()
  ;; another test that the judgment form cache doesn't interfere with build-derivations
  (define-language nats
    (n ::= z (s n)))
  
  (define-judgment-form nats
    #:mode (even I)
    [--------
     "evenz"
     (even z)]
    
    [(even n)
     ---------------- "even2"
     (even (s (s n)))])
  
  (define-judgment-form nats
    #:mode (even2 I)
    [(even n)
     ---------
     (even2 n)])
  (judgment-holds (even2 (s (s z))))
  
  (test (build-derivations (even (s (s z))))
        (list
         (derivation
          '(even (s (s z)))
          "even2"
          (list (derivation '(even z) "evenz" '()))))))

(let ()
  (define-judgment-form empty-language
    #:mode (J O I)
    [------------- "smaller"
     (J any (any))]
    
    [----------------- "bigger"
     (J ((any any)) any)])
  
  (test (judgment-form? J) #t)
  (test (IO-judgment-form? J) #t)
  (test (apply-reduction-relation J '(2))
        (judgment-holds (J any (2)) any))
  (test (apply set (apply-reduction-relation/tag-with-names J '(3)))
        (set (list "smaller" 3)
             (list "bigger" '(((3) (3)))))))

(let ()
  (define-judgment-form empty-language
    #:mode (J I O)
    [------------- "smaller"
     (J (any) any)]
    
    [----------------- "bigger"
     (J any ((any any)))])
  
  (test (judgment-form? J) #t)
  (test (IO-judgment-form? J) #t)
  (test (apply-reduction-relation J '(2))
        (judgment-holds (J (2) any) any))
  (test (apply set (apply-reduction-relation/tag-with-names J '(3)))
        (set (list "smaller" 3)
             (list "bigger" '(((3) (3)))))))

(let ()
  (define-language U
    (n Z (S n)))
  
  (define-judgment-form U
    #:mode (jsum I I I)
    [(jsum n Z n)]
    [(jsum n_1 (S n_2) (S n_3))
     (jsum n_1 n_2 n_3)])
  
  (define-relation U
    sum ⊆ n x n x n
    [(sum n Z n)]
    [(sum n_1 (S n_2) (S n_3))
     (sum n_1 n_2 n_3)])
  
  (define-relation U
    [(rjsum n_1 n_2 n_3)
     (jjsum n_1 n_2 n_3)])
  
  (define-judgment-form U
    #:mode (jjsum I I I)
    [(jjsum n_1 n_2 n_3)
     (rrsum n_1 n_2 n_3)])
  
  (define-relation U
    [(rrsum n_1 n_2 n_3)
     (jsum n_1 n_2 n_3)])
  
  (test (term (sum Z Z Z)) #t)
  (test (term (sum Z Z (S Z))) #f)
  (test (term (sum (S Z) (S Z) (S (S Z)))) #t)
  (test (term (sum (S Z) (S (S Z)) (S (S Z)))) #f)
  (test (term (sum (S (S Z)) (S (S Z)) (S (S (S (S Z)))))) #t)
  (test (term (sum (S (S Z)) (S (S Z)) (S (S (S Z))))) #f)
  (test (term (jsum Z Z Z)) #t)
  (test (term (jsum Z Z (S Z))) #f)
  (test (term (jsum (S Z) (S Z) (S (S Z)))) #t)
  (test (term (jsum (S Z) (S (S Z)) (S (S Z)))) #f)
  (test (term (jsum (S (S Z)) (S (S Z)) (S (S (S (S Z)))))) #t)
  (test (term (jsum (S (S Z)) (S (S Z)) (S (S (S Z))))) #f)
  (test (term (rjsum Z Z Z)) #t)
  (test (term (rjsum Z Z (S Z))) #f)
  (test (term (rjsum (S Z) (S Z) (S (S Z)))) #t)
  (test (term (rjsum (S Z) (S (S Z)) (S (S Z)))) #f)
  (test (term (rjsum (S (S Z)) (S (S Z)) (S (S (S (S Z)))))) #t)
  (test (term (rjsum (S (S Z)) (S (S Z)) (S (S (S Z))))) #f))

(let ()
  (define-judgment-form empty-language
    #:mode (Q I O)
    [(Q number_1 ,(+ (term number_1) (term number_1)))]
    [(Q (number_1 number_2) number_3)
     (Q ,(+ (term number_1) (term number_2)) number_3)])
  
  (test (judgment-holds (Q 1 2))
        #t)
  (test (judgment-holds (Q 1 3))
        #f)
  (test (judgment-holds (Q 1 number_1) number_1)
        '(2))
  (test (judgment-holds (Q 7 14))
        #t)
  (test (judgment-holds (Q 7 symbol))
        #f)
  (test (judgment-holds (Q 7 number_1) number_1)
        '(14))
  (test (judgment-holds (Q (1 2) 6))
        #t)
  (test (judgment-holds (Q (1 3) 6))
        #f)
  (test (judgment-holds (Q (3 4) number_1) number_1)
        '(14)))

(let ()
  (define-judgment-form empty-language
    #:mode (J1 I O)
    [------------
     (J1 1 1)])
  
  (define-judgment-form empty-language
    #:mode (J2 I)
    [(side-condition ,(judgment-holds (J1 any_1 any_2)))
     --------
     (J2 any_1)])
  
  (test (judgment-holds (J2 1)) #t)
  (test (judgment-holds (J2 2)) #f))
  
(let () 
  (define-judgment-form empty-language
    #:mode (J I)
    [(D any_x) ...
     --------------
     (J (any_x ...))])
  (define-judgment-form empty-language
    #:mode (D I)
    [----------- nat
                 (D natural)]
    [----------- num
                 (D number)])
  
  ;; this test is designed to check to see if we are
  ;; avoiding an exponential blow up. On my laptop,
  ;; a list of length 14 was taking 2 seconds before
  ;; the fix and 1 msec afterwards. After the fix,
  ;; a list of length 100 (as below) was also taking 
  ;; no time.
  
  (define-values (_ cpu real gc)
    (time-apply
     (λ ()
       (judgment-holds (J ,(build-list 100 add1))))
     '()))
  (test (< cpu 1000) #t))



(parameterize ([current-namespace (make-base-namespace)])
  (eval '(require errortrace))
  (eval '(require redex/reduction-semantics))
  (eval '(define-language L))
  (eval '(define-judgment-form L
           #:mode (J I)
           [(J a)
            (J b)]
           [(J b)]))
  (test (eval '(judgment-holds (J a))) #t))

(define-namespace-anchor nsa)
(define ns (namespace-anchor->namespace nsa))
(test (parameterize ([current-namespace ns])
        (with-handlers ([exn:fail? (λ (x)
                                     (regexp-match? #rx"lambda[?]: mode spec"
                                                    (exn-message x)))])
          (expand '(module m racket/base
                     (require redex/reduction-semantics)
                     (define-language empty-language)
                     (define-judgment-form empty-language
                       #:mode (lambda? I)
                       #:contract (lambda? any_e)
                       [-----------
                        (lambda? 1)])
                     (define-metafunction empty-language
                       not-lambda? : e -> boolean
                       [(not-lambda? e)
                        #f
                        (judgment-holds (lambda?))]
                       [(not-lambda? e) #t])))))
      #t)

(test (parameterize ([current-namespace ns])
        (with-handlers ([exn:fail? (λ (x)
                                     (regexp-match? #rx"lambda[?]: mode spec"
                                                    (exn-message x)))])
          (expand '(module m racket/base
                     (require redex/reduction-semantics)
                     (define-language empty-language)
                     (define-judgment-form empty-language
                       #:mode (lambda? I)
                       #:contract (lambda? any_e)
                       [-----------
                        (lambda? 1)])
                     (judgment-holds (lambda?))))))
      #t)

(print-tests-passed 'tl-judgment-form.rkt)
