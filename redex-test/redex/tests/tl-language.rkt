#lang racket
(require "private/test-util.rkt"
         redex/reduction-semantics
         (only-in redex/private/lang-struct
                  make-bindings make-bind
                  compiled-lang-lang compiled-lang-cclang
                  nt-rhs nt-name rhs-pattern)
         racket/match
         (for-syntax redex/private/term-fn racket/base))

(define-namespace-anchor ns-anchor)
(define ns (namespace-anchor->namespace ns-anchor))

(module test racket/base)
(reset-count)

(define-syntax (language-aliases stx)
  (syntax-case stx ()
    [(_ x)
     (with-syntax ([x (language-id-nt-aliases #'x 'aliases)])
       #''x)]))

(define (language-nts-as-set lang)
  (for/set ([nt (in-list (compiled-lang-lang lang))])
    (nt-name nt)))

(define (language-cross-nts lang)
  (for/set ([nt (in-list (compiled-lang-cclang lang))])
    (nt-name nt)))

(define (get-bad-nt-references lang aliases)
  (define not-really-nts (set))
  (define nts (language-nts-as-set lang))
  (for ([nt (in-list (compiled-lang-lang lang))])
    (for ([rhs (in-list (nt-rhs nt))])
      (let loop ([pat (rhs-pattern rhs)])
        (match pat
          [`(nt ,n)
           (unless (set-member? nts n)
             (set! not-really-nts (set-add not-really-nts n)))]
          [(? list?)
           (for ([pat (in-list pat)])
             (loop pat))]
          [_ (void)]))))
  not-really-nts)

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

(test (let ([m (redex-match 
                empty-language
                (side-condition (any_1 ...) #t)
                '())])
        (and m
             (= 1 (length m))
             (match-bindings (car m))))
      (list (make-bind 'any_1 '())))

(test (pair? (redex-match grammar M '(1 1))) #t)
(test (pair? (redex-match grammar M '(1 1 1))) #f)
(test (pair? (redex-match grammar
                          (side-condition (M_1 M_2) (equal? (term M_1) (term M_2)))
                          '(1 1)))
      #t)
(test (pair? (redex-match grammar
                          (side-condition (M_1 M_2) (equal? (term M_1) (term M_2))) 
                          '(1 2)))
      #f)

(test (pair? ((redex-match grammar M) '(1 1)))
      #t)

(test (pair? (redex-match grammar (name not-an-nt_subscript 1) 1)) #t)

;; next 3: test naming of subscript-less non-terminals
(test (pair? (redex-match grammar (M M) (term (1 1)))) #t)
(test (pair? (redex-match grammar (M M) (term (1 2)))) #f)
(test (pair? (redex-match grammar (M_1 M_2) (term (1 2)))) #t)

(define-language base-grammar
  (q 1)
  (e (+ e e) number)
  (x (variable-except +)))

(define-extended-language extended-grammar
  base-grammar 
  (e .... (* e e))
  (x (variable-except + *))
  (r 2))

(test (pair? (redex-match extended-grammar e '(+ 1 1))) #t)
(test (pair? (redex-match extended-grammar e '(* 2 2))) #t)
(test (pair? (redex-match extended-grammar r '2)) #t)
(test (pair? (redex-match extended-grammar q '1)) #t)
(test (pair? (redex-match extended-grammar x '*)) #f)
(test (pair? (redex-match extended-grammar x '+)) #f)
(test (pair? (redex-match extended-grammar e '....)) #f)

;; make sure that `language' with a four period ellipses signals an error
(test (regexp-match #rx"[.][.][.][.]" (with-handlers ([exn? exn-message]) 
                                        (let ()
                                          (define-language x (e ....))
                                          12)))
      '("...."))

(let ()
  ; non-terminals added by extension can have underscores
  (define-extended-language L base-grammar
    (z () (1 z_1 z_1)))
  (test (redex-match L z (term (1 () (1 () ())))) #f))

;; test multiple variable non-terminals
(let ()
  (define-language lang
    ((l m) (l m) x)
    (x variable-not-otherwise-mentioned))
  (test (pair? (redex-match lang m (term x)))
        #t))

;; test multiple variable non-terminals
(let ()
  (define-language lang
    ((l m) (l m) x)
    (x variable-not-otherwise-mentioned))
  (test (pair? (redex-match lang l (term x)))
        #t))

(let ()
  (define-language L
    [Cv (name n variable-not-otherwise-mentioned)])
  (test (redex-match L Cv (term ())) #f)
  (test (pair? (redex-match L Cv (term x))) #t))

(let ()
  (define-language lang
    ((x y) 1 2 3))
  (define-extended-language lang2 lang
    (x .... 4))
  (test (pair? (redex-match lang2 x 4)) #t)
  (test (pair? (redex-match lang2 y 4)) #t)
  (test (pair? (redex-match lang2 x 1)) #t)
  (test (pair? (redex-match lang2 y 2)) #t))

;; test that the variable "e" is not bound in the right-hand side of a side-condition
;; this one signaled an error at some point
(let ()
  (define-language bad
    (e 2 (side-condition (e) #t)))
  (test (pair? (redex-match bad e '(2)))
        #t))

;; test that the variable "e" is not bound in the right-hand side of a side-condition
;; this one tests to make sure it really isn't bound
(let ([x #f])
  (define-language bad
    (e 2 (side-condition (e) (set! x (term e)))))
  (redex-match bad e '(2))
  (test x 'e))

;; test multiple variable non-terminals being extended
(let ()
  (define-language lang
    ((x y) 1 2 3))
  (define-extended-language lang2 lang
    (x .... 4))
  (test (pair? (redex-match lang2 x 4)) #t)
  (test (pair? (redex-match lang2 y 4)) #t)
  (test (pair? (redex-match lang2 x 1)) #t)
  (test (pair? (redex-match lang2 y 2)) #t))

;; test multiple variable non-terminals in an extended language
(let ()
  (define-language lang
    ((x y) 1 2 3))
  (define-extended-language lang2 lang
    ((z w) 5 6 7))
  (test (language-aliases lang2) (hash 'y 'x 'w 'z))
  (test (pair? (redex-match lang2 z 5)) #t)
  (test (pair? (redex-match lang2 w 6)) #t))

;; test cases that ensure that extending any one of a
;; multiply defined non-terminal gets extended properly
(let ()
  (define-language iswim
    ((V U W) AA))
  
  (define-extended-language iswim-cont
    iswim
    (W .... QQ))
  
  (test (pair? (redex-match iswim-cont U (term QQ)))
        #t))

(let ()
  (define-language iswim
    ((V U W) AA))
  
  (define-extended-language iswim-cont
    iswim
    (W .... QQ))
  
  (test (pair? (redex-match iswim-cont V (term QQ)))
        #t)
  (test (pair? (redex-match iswim-cont U (term QQ)))
        #t)
  (test (pair? (redex-match iswim-cont W (term QQ)))
        #t))

(let ()
  (define-language iswim
    ((V U W) AA))
  
  (define-extended-language iswim-cont
    iswim
    (V .... QQ))
  
  (test (pair? (redex-match iswim-cont V (term QQ)))
        #t)
  (test (pair? (redex-match iswim-cont U (term QQ)))
        #t)
  (test (pair? (redex-match iswim-cont W (term QQ)))
        #t))

(let ()
  (define-language okay
    [(X Y) z])
  
  (define-extended-language replace-both
    okay
    [(X Y) q])
  
  ;; this test ran into an infinite loop in an earlier version of redex.
  (test (redex-match replace-both X (term explode)) #f))

(let () 
  (define-language main
    [(X Y) z])
  (define-extended-language new
    main
    [(X Y Z) q])
  (test (language-aliases main) (hash 'Y 'X))
  (test (language-aliases new) (hash 'Y 'X 'Z 'X)))

(test (with-handlers ([exn:fail:syntax? exn-message])
        (parameterize ([current-namespace ns])
          (expand '(let () 
                     (define-language main
                       [(X Y) z]
                       [(P Q) w])
                     (define-extended-language new
                       main
                       [(X P) q])
                     (void)))))
      (regexp
       (regexp-quote
        (string-append
         "define-extended-language: new language does not have the same non-terminal"
         " aliases as the old;\n non-terminal X was not in the same group"
         " as P in the original language"))))

(test (with-handlers ([exn:fail:syntax? exn-message])
        (parameterize ([current-namespace ns])
          (expand '(let ()
                     (define-language base
                       (e ::=
                          done
                          (par& e ...))
                       (E ::= (in-hole ECM1 E))
                       (ECM1 ::= (par& hole e e ...)))

                     (λ (x)
                       (redex-match base
                                    (in-hole E (par& e_1 ... done e_2 ...))
                                    x))))))
      (regexp
       (regexp-quote
        (string-append
         "in-hole's first argument is expected to match"
         " exactly one hole, but it cannot match a hole"))))


;; underscores in literals
(let ()
  (define-language L
    (x (variable-except a_b))
    (y (variable-prefix a_b)))
  (test (pair? (redex-match L x (term a_c))) #t)
  (test (pair? (redex-match L y (term a_bc))) #t))

; underscores allowed on built-in non-terminals and names bound
(let ([m (redex-match 
          grammar 
          (any_1 number_1 natural_1 integer_1
                 real_1 string_1 variable_1
                 variable-not-otherwise-mentioned_1)
          '(1 2 3 4 5 "s" s t))])
  (test (if m
            (map bind-exp
                 (sort (match-bindings (car m))
                       string<=?
                       #:key (compose symbol->string bind-name)))
            '())
        '(1 4 3 2 5 "s" t s)))

(let ()
  (define-language L
    (e (e e) number))
  ;; not a syntax error since first e is not a binder
  (test (pair? (redex-match L ((cross e) e ...) (term ((hole 2) 1)))) #t))

;; match structures do not report ..._x bindings
(test (map match-bindings (redex-match grammar (a ..._1) (term (a a a))))
      '(()))

;; make sure redex-match? does the equality check
(test (redex-match? empty-language (any_0 any_0) (term (1 2))) #f)

(define-syntax (test-match stx)
  (syntax-case stx ()
    [(_ actual (((var val) ...) ...))
     (syntax/loc stx
       (test (apply
              set
              (for/list ([match actual])
                (for/list ([bind (match-bindings match)])
                  (list (bind-name bind) (bind-exp bind)))))
             (apply set (list (list (list 'var (term val)) ...) ...))))]))

;; cross
(let ()
  (define-language L
    (e (e e)
       (cont (hide-hole E))
       number
       x)
    (E hole
       (e ... E e ...))
    (x variable-not-otherwise-mentioned))
  (test-match 
   (redex-match 
    L 
    (in-hole (cross e) e)
    (term (cont (1 hole))))
   (((e (cont (1 hole))))
    ((e 1)))))
(let ()
  (define-language L
    (e (e e ...)
       x
       v)
    (v (λ (x ...) e)
       cont-val
       number)
    (cont-val (cont (hide-hole E)))
    (E hole
       (in-hole L E))
    (L (v ... hole e ...))
    (x variable-not-otherwise-mentioned))
  
  ;; no "found two holes" error
  (test (redex-match L (cross e) (term (cont ((λ (x) x) hole)))) #f)
  
  (test-match 
   (redex-match 
    L 
    (in-hole (cross e) e)
    (term ((cont ((λ (x) x) hole)) (λ (y) y))))
   (((e x))
    ((e ((cont ((λ (x) x) hole)) (λ (y) y))))
    ((e y))
    ((e (λ (y) y)))
    ((e (cont ((λ (x) x) hole)))))))

;; test caching
(let ()
  (define match? #t)
  
  (define-language lang
    (x (side-condition any match?)))
  
  (test (pair? (redex-match lang x 1)) #t)
  (set! match? #f)
  (test (pair? (redex-match lang x 1)) #t)
  (parameterize ([caching-enabled? #f])
    (test (pair? (redex-match lang x 1)) #f)))


(let ()
  (define sc-eval-count 0)
  (define-language lang
    (x (side-condition any (begin (set! sc-eval-count (+ sc-eval-count 1))
                                  #t))))
  
  (redex-match lang x 1)
  (redex-match lang x 1)
  (parameterize ([caching-enabled? #f])
    (redex-match lang x 1))
  (test sc-eval-count 2))

(let ()
  (define rhs-eval-count 0)
  (define-metafunction empty-language
    [(f any) ,(begin (set! rhs-eval-count (+ rhs-eval-count 1))
                     1)])
  
  (term (f 1))
  (term (f 1))
  (parameterize ([caching-enabled? #f])
    (term (f 1)))
  (test rhs-eval-count 2))

(let ()
  (define-language L)
  (define-extended-language E L
    (v ((bar X_1) X_1))
    ((X Y) any))
  (test (and (redex-match E v (term ((bar 1) 1))) #t) #t)
  (test (redex-match E v (term ((bar 1) 2))) #f))

(let ()
  (define-language L
    (M N ::= (M N) (λ (x) M) x)
    (x ::= variable-not-otherwise-mentioned))
  (test (and (redex-match L M '(λ (x) (x x))) #t) #t)
  (test (and (redex-match L N '(λ (x) (x x))) #t) #t)
  (define-extended-language L+ L
    (M ::= .... n)
    (n m ::= number))
  (test (and (redex-match L+ M '(λ (x) 7)) #t) #t)
  (test (and (redex-match L+ m 7) #t) #t)
  (let ([::= void])
    (define-language L
      (::= () (number ::=)))
    (test (and (redex-match L ::= '(1 ())) #t) #t)))

(let ()
  (define-language L1
    ((q x) 1 2 3)
    ((y w) 4 5 6 x)
    (z 7 8 9))
  
  (define-language L2
    ((x y) 100 101 102)
    (b 103 x))
  
  (define-union-language L L1 (- L2))
  
  (test (and (redex-match L x 3) #t) #t)
  (test (and (redex-match L y 2) #t) #t)
  (test (redex-match L x 100) #f)
  (test (and (redex-match L -x 100) #t) #t)
  (test (and (redex-match L -b 100) #t) #t)
  (test (redex-match L -b 3) #f))

;; The following two tests make sure that `define-union-language`
;; works with extended languages
(let ()
  (define-language LBase
    (e (+ e e)
       number))
  
  (define-extended-language L1 LBase
    (e ....
       (- e e)))
  
  (define-extended-language L2 LBase
    (e ....
       (* e e)))
  
  (define-union-language LMerge (one. L1) (two. L2))
  
  #|
    The error that used to be raised:
    define-union-language: two sublanguages both contribute the non-terminal: one.e in:
      (one. L1)
      (one. L1)
    |#
  
  
  (test (and (redex-match LMerge one.e (term (- 0 0))) #t) #t)
  (test (and (redex-match LMerge two.e (term (* 0 0))) #t) #t)
  
  (define-union-language LMergeUntagged L1 L2)
  
  (for ([t (list (term 1) (term (* 1 1)) (term (+ 1 1)) (term (- 1 1)))])
    (test (redex-match? LMergeUntagged e t) #t)))

;; test that define-union-language properly merges non-terminals
(let () 
  (define-language LBase
    (e (+ e e) number))
  
  (define-extended-language L1 LBase
    (e ....  (- e e)))
  
  (define-extended-language L2 LBase
    (e ....  (* e e)))
  
  ;; Untagged union of two languages that define the same nonterminal
  (define-union-language LMergeUntagged L1 L2)
  
  ;; Tagged merge of two extended languages that define the same
  ;; nonterminal
  (define-union-language LMergeTagged (f. L1) (d. L2))
  
  (test (redex-match? LMergeUntagged e (term 1)) #t)
  (test (redex-match? LMergeUntagged e (term (* 1 1))) #t)
  (test (redex-match? LMergeUntagged e (term (+ 1 1))) #t)
  (test (redex-match? LMergeUntagged e (term (- 1 1))) #t)
  
  (test (redex-match? LMergeTagged f.e 1) #t)
  (test (redex-match? LMergeTagged d.e 1) #t)
  
  (test (redex-match? LMergeTagged f.e (term (+ 1 1))) #t)
  (test (redex-match? LMergeTagged f.e (term (- 1 1))) #t)
  (test (redex-match? LMergeTagged f.e (term (* 1 1))) #f)
  
  (test (redex-match? LMergeTagged d.e (term (+ 1 1))) #t)
  (test (redex-match? LMergeTagged d.e (term (* 1 1))) #t)
  (test (redex-match? LMergeTagged d.e (term (- 1 1))) #f))

(let ()
  (define-language L1 (e f ::= 1))
  (define-language L2 (e g ::= 2))
  (define-union-language Lc L1 L2)
  (test (redex-match? Lc e 1) #t)
  (test (redex-match? Lc e 2) #t)
  (test (redex-match? Lc f 1) #t)
  (test (redex-match? Lc f 2) #t)
  (test (redex-match? Lc g 1) #t)
  (test (redex-match? Lc g 2) #t))

(let ()
  (define-language UT
    (e (e e)
       (λ (x) e)
       x))
  
  (define-language WT
    (e (e e)
       (λ (x t) e)
       x)
    (t (→ t t)
       num))
  
  (define-extended-language UT+ UT
    (e ....
       (foo e e)))
  
  (define-union-language B (ut. UT+) (wt. WT))
  
  (test (and (redex-match B ut.e (term (foo x x))) #t) #t)
  (test (redex-match B wt.e (term (foo x x))) #f))

(let ()
  (test (redex-match empty-language number 'a) #f)
  (test (redex-match empty-language (in-hole hole number) 'a) #f))

(let ()
  (define-language L
    (a number)
    (b (a a))
    (c (b b)))
  (test (term 1 #:lang L) 1)
  (test (term ((1 2) (3 4)) #:lang L) '((1 2) (3 4)))
  (test (term (1 2 3 4) #:lang L) '(1 2 3 4))
  (test (redex-let L ([a_1 5])
                   (term (a_1 6) #:lang L))
        '(5 6))
  (test (redex-let L ([number_1 5])
                   (term (number_1 6) #:lang L))
        '(5 6)))

;; make sure the "before underscore" check works (no syntax error)
(let ()
  (define-extended-language L2 empty-language [(τ υ) whatever])
  (test (begin (term υ_1 #:lang L2) (void))
        (void)))

;; make sure the "before underscore" check works (no syntax error)
(let ()
  (define-language L1 [x y ::= variable])
  (define-language L2 [n m ::= natural])
  (define-union-language L (: L1) (^ L2))
  (test (begin (term :x_1 #:lang L) (void)) (void))
  (test (begin (term ^n_1 #:lang L) (void)) (void)))

(let ()
  ;; test to make sure that reasonable short-circuiting is happening
  ;; when matching lists of differing length to avoid exponential behavior
  
  ;; this test is fragile because it is based on cpu times.
  ;; on my machine, with the bug in place it takes 2000+ msec
  ;; to run and with the fix it takes 200 or so msec.
  
  (define-language abort-core-lang
    (e integer
       (- e)
       (- e e)))
  
  (define (add-minuses t count)
    (let loop ([i count])
      (cond
        [(zero? i) t]
        [else `(- ,(loop (- i 1)))])))
  
  
  (define-values (answer cpu real gc) 
    (time-apply
     (λ ()
       (parameterize ([caching-enabled? #f])
         (for ([count (in-range 20)])
           (redex-match abort-core-lang
                        e
                        (add-minuses 11 count)))))
     '()))
  (test (< cpu 1000) #t))

(let ()
  ;; _ as a non-binding match
  (define-language L)
  
  (test (pair? (redex-match L _ '(1 2 3)))
        #t)
  (test (redex-match L (_ _) '(1 2 3))
        #f)
  (test (pair? (redex-match L (_ _ ...)'(1 2)))
        #t)
  (test (redex-match L (_ _ ...)'())
        #f)
  (test (pair? (redex-match L (_ (_ _ ...) ...) '((1 2) (3 4) (5 6))))
        '#t)
  (test (redex-match L (_ (_ _ ...) ...) '((1 2) (3 4) () (5 6)))
        #f))


(let ()
  (test (and (redex-match
              empty-language
              (natural ..._r)
              (term ()))
             #t)
        #t))


;                                                                 
;                                                                 
;                    ;;                        ;;                 
;                     ;                         ;            ;    
;   ;; ;;   ;;;    ;; ;   ;;;  ;;  ;;           ;     ;;;   ;;;;; 
;    ;;    ;   ;  ;  ;;  ;   ;  ;  ;            ;    ;   ;   ;    
;    ;     ;;;;;  ;   ;  ;;;;;   ;;    ;;;;;    ;    ;;;;;   ;    
;    ;     ;      ;   ;  ;       ;;             ;    ;       ;    
;    ;     ;      ;   ;  ;      ;  ;            ;    ;       ;   ;
;   ;;;;;   ;;;;   ;;;;;  ;;;; ;;  ;;         ;;;;;   ;;;;    ;;; 
;                                                                 
;                                                                 
;                                                                 
;                                                                 

(let ()
  (define-language L
    (n number)
    (x variable))
  
  (test (redex-let L ([(n_1 n_2) '(1 2)])
                   (term (n_2 n_1)))
        (term (2 1)))
  (test (redex-let L ([(x_i ([x_0 n_0] ... [x_i n_i] [x_i+1 n_i+1] ...))
                       '(b ([a 1] [b 2] [c 3]))])
                   (term n_i))
        2)
  (test (with-handlers ([exn:fail:redex? exn-message])
          (redex-let L ([(n) 1]) 'no-exn))
        "redex-let: term 1 does not match pattern (n)")
  (test (with-handlers ([exn:fail:redex? exn-message])
          (redex-let L ([(n_1 ... n_i n_i+1 ...) '(1 2 3)]) 'no-exn))
        "redex-let: pattern (n_1 ... n_i n_i+1 ...) matched term (1 2 3) multiple ways")
  (test (redex-let L ([n_1 1])
                   (redex-let L ([n_1 2] [n_2 (term n_1)])
                              (term (n_1 n_2))))
        (term (2 1)))
  (test (redex-let L ([n_1 1])
                   (redex-let* L ([n_1 2] [n_2 (term n_1)])
                               (term (n_1 n_2))))
        (term (2 2)))
  
  (test (redex-let L ([(n_1 n_1) '(1 1)]) (term n_1))
        1)
  (test
   (redex-let* L ([(n_1) '(1)] [n_1 1]) (term n_1))
   1))

(let ()
  (test (redex-let empty-language ([(any_1 ..._1) (list 4 5 6)])
                   (term (0 ..._1)))
        '(0 0 0))
  
  (define-metafunction empty-language
    [(f any_x) (any_x any_x)])
  
  (test (redex-let empty-language ([(any_1 ..._1) (list 4 5 6)])
                   (term ((f 0) ..._1)))
        (term ((0 0) (0 0) (0 0))))
  
  (test (redex-let empty-language ([(any_1 ..._1) (list 4 5 6)])
                   (term ((f ("1" "2")) ..._1)))
        (term ((("1" "2") ("1" "2"))
               (("1" "2") ("1" "2"))
               (("1" "2") ("1" "2"))))))

(let ()
  (define-language A
    (e ::= 1))
  
  (define-extended-language B A
    (fred ::= 0))
  
  (define err-msg
    (with-handlers ([exn:fail? exn-message])
      (compatible-closure
       (reduction-relation B (--> fred fred))
       A ;; should've been B
       e)
      "no error raised"))
  
  (test #t (regexp-match? #rx"^compatible-closure:.*fred" err-msg)))

(let ()
  (define-language L1)
  (define-language L2)
  (define-union-language L3 L1 L2)
  (define-extended-language L4 L3)
  (void))

(let ()
  (define-language L1
    [x y ::= number])
  (define-language L2
    [x ::= variable])
  (define-union-language L L1 L2)
  (test (language-nts L1) (list 'x 'y))
  (test (language-nts L2) (list 'x))
  (test (language-nts L) (list 'x 'y))
  (test (redex-match? L y 0) #t)
  (test (redex-match? L y 'x) #t)
  (test (language-aliases L) (hash 'y 'x))
  (test (language-nts-as-set L) (set 'x))
  (test (language-cross-nts L) (set 'x-x))
  (test (get-bad-nt-references L (language-aliases L))
        (set)))

(let ()
  (define-language L1
    [x y ::= number])
  (define-language L2
    [y z ::= variable])
  (define-union-language L L1 L2)
  (test (language-aliases L) (hash 'y 'x 'z 'x))
  (test (language-nts-as-set L) (set 'x))
  (test (language-cross-nts L) (set 'x-x))
  (test (get-bad-nt-references L (language-aliases L))
        (set)))

(let ()
  (define-language L1
    [x y ::= number (x y)])
  (define-language L2
    [y z ::= variable (y z)])
  (define-union-language L L1 L2)
  (test (language-aliases L) (hash 'y 'x 'z 'x))
  (test (language-nts-as-set L) (set 'x))
  (test (language-cross-nts L) (set 'x-x))
  (test (get-bad-nt-references L (language-aliases L))
        (set)))

(let ()
  (define-language L1
    [x y ::= number (X x) (Y y)])
  (define-language L2
    [oy z ::= variable (OY oy) (Z z)])
  (define-union-language L (o L1) L2)
  (test (language-aliases L) (hash 'oy 'ox 'z 'ox))
  (test (language-nts-as-set L) (set 'ox))
  (test (get-bad-nt-references L (language-aliases L))
        (set)))

(let ()
  (define-language L1)
  (define-extended-language L2 L1 (P Q ::= 1))
  (define-language L3)
  (define-union-language L4 L2 (o L3))
  (test (language-aliases L4) (hash 'Q 'P))
  (test (get-bad-nt-references L4 (language-aliases L4))
        (set)))

(let ()
  (define-language L1)
  (define-extended-language L2 L1 (P Q ::= 1))
  (define-language L3)
  (define-extended-language L4 L3 (R S ::= 1))
  (define-union-language L5 L2 (: L4))
  (test (language-aliases L5) (hash 'Q 'P ':S ':R))
  (test (get-bad-nt-references L5 (language-aliases L5))
        (set)))

(let ()
  (define-language L1)
  (define-extended-language L2 L1 (P Q ::= 1))
  (define-language L3)
  (define-extended-language L4 L3 (P Q ::= 1))
  (define-union-language L5 L2 (: L4))
  (test (language-aliases L5) (hash 'Q 'P ':Q ':P))
  (test (get-bad-nt-references L5 (language-aliases L5))
        (set)))

(test (let ()
        (define-term x 1)
        (term (x x)))
      (term (1 1)))
(test (let ()
        (define-term x 1)
        (let ([x 'whatever])
          (term (x x))))
      (term (x x)))

 (test (variable-not-in (term (x y z)) 'x)
      (term x1))

(test (variable-not-in (term (y z)) 'x)
      (term x))
(test (variable-not-in (term (x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) 'x)
      (term x11))
(test (variable-not-in (term (x x11)) 'x)
      (term x1))
(test (variable-not-in (term (x x1 x2 x3)) 'x1)
      (term x4))
(test (variable-not-in (term (x x1 x1 x2 x2)) 'x)
      (term x3))
(test (variable-not-in (term (|| |1|)) '||) '|2|)

(test (variables-not-in (term (x y z)) '(x))
      '(x1))
(test (variables-not-in (term (x2 y z)) '(x x x))
      '(x x1 x3))

(test ((term-match/single empty-language
                          [(variable_x variable_y)
                           (cons (term variable_x)
                                 (term variable_y))])
       '(x y))
      '(x . y))

(test ((term-match/single empty-language
                          [(side-condition (variable_x variable_y)
                                           (eq? (term variable_x) 'x))
                           (cons (term variable_x)
                                 (term variable_y))])
       '(x y))
      '(x . y))

(test ((term-match/single empty-language [() 'a] [() 'b])
       '())
      'a)

(test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                      ((λ (x) #t) (λ (x) 'wrong-exn)))
        ((term-match/single empty-language
                            [(number_1 ... number_2 ...) 1])
         '(1 2 3))
        'no-exn)
      'right-exn)

(test (with-handlers ((exn:fail:redex? (λ (x) 'right-exn))
                      ((λ (x) #t) (λ (x) 'wrong-exn)))
        ((term-match/single empty-language
                            [(number_1 ... number_2 ...) 1])
         'x)
        'no-exn)
      'right-exn)

(test ((term-match empty-language
                   [(number_1 ... number_2 ...) 1])
       'x)
      '())

(define-language x-is-1-language
  [x 1])

(test ((term-match/single x-is-1-language
                          [(x x)
                           1])
       '(1 1))
      1)

(test (call-with-values
       (λ () 
         ((term-match/single empty-language
                             [() (values 1 2)])
          '()))
       list)
      '(1 2))

(test (let ([x 0])
        (cons ((term-match empty-language
                           [(any_a ... number_1 any_b ...)
                            (begin (set! x (+ x 1))
                                   (term number_1))])
               '(1 2 3))
              x))
      '((1 2 3) . 3))

(test ((term-match empty-language
                   [number_1
                    (term number_1)]
                   [number_1
                    (term number_1)])
       '1)
      '(1 1))

(define-syntax (get-nt-hole-map stx)
  (syntax-case stx ()
    [(_ lang)
     (identifier? #'lang)
     #`(hash-copy '#,(language-id-nt-hole-map #'lang 'get-nt-hole-map))]))

(test (get-nt-hole-map empty-language) (make-hash))

(let ()
  (define-language L
    (e ::= (e e) x (λ (x) e))
    (x ::= variable-not-otherwise-mentioned))
  (test (get-nt-hole-map L)
        (make-hash '((e . 0) (x . 0)))))

(let ()
  (define-language L
    (e ::= (e e) x (λ (x) e))
    (x ::= variable-not-otherwise-mentioned)
    (E ::= (e E) (E e) hole))
  (test (get-nt-hole-map L)
        (make-hash '((e . 0) (x . 0) (E . 1)))))

(let ()
  (define-language L
    (E ::= hole (E ...)))
  (test (get-nt-hole-map L) (make-hash '((E . lots)))))

(let ()
  (define-language L
    (E ::= hole))
  
  (define-extended-language L2 L
    (E ::= ....))
  
  (test (get-nt-hole-map L2) (make-hash '((E . 1)))))

(let ()
  (define-language L
    (e ::= (e e) x (λ (x) e))
    (x ::= variable-not-otherwise-mentioned))
  
  (define-extended-language L2 L
    (E ::= (e E) (E e) hole))
  
  (test (get-nt-hole-map L2) (make-hash '((e . 0) (x . 0) (E . 1)))))

(let ()
  (define-language L
    (E hole
       (in-hole L E))
    (L (hole)))
  (test (get-nt-hole-map L) (make-hash '((L . 1) (E  . 1)))))

(let ()
  (define-language L1)
  (define-extended-language L2 L1
    ((l k) Zz))
  (define-extended-language L3 L2
    ((k l) .... Yy))
  (test (redex-match? L3 k (term Zz)) #t)
  (test (redex-match? L3 k (term Yy)) #t)
  (test (redex-match L3 k (term Aa)) #f))

(let ()
  (define-language L1
    [x y ::= number]
    [z ::= whatever])
  (define-extended-language L2 L1
    [x y ::= .... variable])
  (test (language-aliases L2) (hash 'y 'x))
  (test (language-nts-as-set L2) (set 'x 'z))
  (test (get-bad-nt-references L2 (language-aliases L2)) (set)))

(let ()
  (define-language L1
    [x y ::= number]
    [z ::= whatever])
  (define-extended-language L2 L1
    [y x ::= .... variable])
  (test (language-aliases L2) (hash 'y 'x))
  (test (language-nts-as-set L2) (set 'x 'z))
  (test (get-bad-nt-references L2 (language-aliases L2)) (set)))

(let ()
  (define-language L
    (A ::= (hole x_1) (hole x_1 (in-hole A x_1)))
    (x ::= variable-not-otherwise-mentioned))
  (test (redex-match? L (in-hole A x) (term (y z (z t)))) #t))  

(let ()
  (define-language L1
    (v ::= (clo [x any_1] any) number)
    (x ::= variable-not-otherwise-mentioned)
    #:binding-forms
    (clo [x _] v #:refers-to x))

  (define-language L2
    (v ::= (clo [x any_1] any) number)
    (x ::= variable-not-otherwise-mentioned)
    #:binding-forms
    (clo [x any] v #:refers-to x))

  (define example-v (term (clo [x 3] 2)))

  (test (redex-match? L1 (clo [x v_0] any_1) example-v) #t)

  (test (redex-match? L2 (clo [x v_0] any_1) example-v) #t))

(let ()
  (define-language L
    (v ::=
       (clo σ v)
       number)
    (σ ::= [x v])
    (x ::= variable-not-otherwise-mentioned)
    #:binding-forms
    (clo [x _] v #:refers-to (shadow x)))
  ;;        ⬑ problem here

  (define example-v (term (clo [x 3] 2)))
  
  (test (redex-match? L v example-v) #t)
  (test (redex-match? L (clo [x v_0] v_1) example-v) #t))

(let ()
  (define-language L
    [x ::= variable-not-otherwise-mentioned]
    [e ::= x null (cons e e) (λ p e)]
    [p ::= x null (cons p p)]
    #:binding-forms
    (λ p e #:refers-to p)
    (cons p_1 p_2) #:exports (shadow p_1 p_2))

  (test (term (substitute (λ null null) x y) #:lang L)
        '(λ null null)))


(let ()
  (define-language esterel
    (pdotdot ::= pdot p)

    (p ::= nothing)

    (pdot ::= (· p))

    (M (machine pdotdot bindings))
    (bindings (s ...))

    #:binding-forms
    (machine pdotdot #:refers-to bindings
             bindings #:refers-to pdotdot))

  (test (redex-match? esterel M (term (machine nothing ())))
        #t)
  (test (redex-match? esterel (machine nothing ()) (term (machine nothing ())))
        #t)

  (test (redex-match? esterel (machine pdotdot bindings) (term (machine nothing ())))
        #t))

(let ()
  (define-language typed-syndicate
    (S hello)
    (P ★)
    (l (λ (P S)))
    #:binding-forms
    (λ (P S #:refers-to P) ...))

  (test (redex-match? typed-syndicate (λ P S) (term (λ ★ hello)))
        #t)
  (test (redex-match? typed-syndicate (λ (P S)) (term (λ (★ hello))))
        #t))

(let ()
  (define-language L1)
  (define-language L2)
  (define-language L3)
  (test (format "~a" (list L1 L2 L3))
        "(#<language: L1> #<language: L2> #<language: L3>)"))

(let ()
  (define-language L
    (e ::= (e e) (λ (x) e) x)
    (x ::= variable-not-otherwise-mentioned)
    #:binding-forms
    (λ (x) e #:refers-to x))

  (define ht (make-binding-hash L))
  (dict-set! ht (term (λ (x) x)) 1)
  (test (dict-ref ht (term (λ (y) y))) 1)

  (test (dict-ref (make-binding-hash L (list (cons (term (λ (x) (x y)))
                                                   1)))
                  (term (λ (z) (z y))))
        1)

  (test (dict-ref (make-immutable-binding-hash L (list (cons (term (λ (x) (x y)))
                                                             1)))
                  (term (λ (z) (z y))))
        1))

(let ()
  (define-language L
    [e ::= (e e) #f]
    [E ::= (cross e)])
  
  (test (pair? (redex-match L (in-hole (cross e) 11)
                            '(((11 #f) #f) #f)))
        #t))

(let ()
  (define-language L
    [e ::= (e e) #f]
    [E ::= (cross e)])

  (test (pair? (redex-match L (in-hole E 11)
                            '(((11 #f) #f) #f)))
        #t))



(let ()
  (define-language L
    [e ::= (e e) #f]
    [E ::= (compatible-closure-context e)])

  (test (pair? (redex-match L (in-hole (cross e) 11)
                            '(((11 #f) #f) #f)))
        #t))

(let ()
  (define-language L
    [e ::= (e e) #f]
    [E ::= (compatible-closure-context e)])

  (test (pair? (redex-match L (in-hole E 11)
                            '(((11 #f) #f) #f)))
        #t))

(let ()
  (define-language L
    [e ::= v x (e e)]
    [v ::= (λ (x) e) add1 natural])

  (test (pair? (redex-match L
                            (in-hole (compatible-closure-context v #:wrt e)
                                     1)
                            (term (λ (x) 1))))
        #t))

(let ()
  (define-language L
    [t ::= (λ (x) t) (t v) (force v) (return v)]
    [v ::= (thunk t)])

  (test (pair? (redex-match L
                            (in-hole (compatible-closure-context v #:wrt t) 11)
                            '(thunk (λ (x) 11))))
        #t)

  (test (pair? (redex-match L
                            (in-hole (compatible-closure-context t #:wrt v) 11)
                            '(thunk (λ (x) 11))))
        #f))

(print-tests-passed 'tl-language.rkt)
