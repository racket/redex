#lang racket
(require "private/test-util.rkt"
         redex/reduction-semantics
         (only-in redex/private/lang-struct make-bindings make-bind)
         racket/match
         redex/private/struct)

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


(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (--> (in-hole E_1 (number_1 number_2))
             (in-hole E_1 ,(* (term number_1) (term number_2)))))
       '((2 3) (4 5)))
      (list '(6 (4 5))))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (~~> (number_1 number_2)
             ,(* (term number_1) (term number_2)))
        with
        [(--> (in-hole E_1 a) (in-hole E_1 b)) (~~> a b)])
       '((2 3) (4 5)))
      (list '(6 (4 5))))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (==> (number_1 number_2)
             ,(* (term number_1) (term number_2)))
        with
        [(--> (M_1 a) (M_1 b)) (~~> a b)]
        [(~~> (M_1 a) (M_1 b)) (==> a b)])
       '((1 2) ((2 3) (4 5))))
      (list '((1 2) ((2 3) 20))))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (~~> (number_1 number_2)
             ,(* (term number_1) (term number_2)))
        (==> (number_1 number_2)
             ,(* (term number_1) (term number_2)))
        with
        [(--> (M_1 a) (M_1 b)) (~~> a b)]
        [(--> (a M_1) (b M_1)) (==> a b)])
       '((2 3) (4 5)))
      (list '(6 (4 5))
            '((2 3) 20)))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (--> (M_1 (number_1 number_2))
             (M_1 ,(* (term number_1) (term number_2))))
        (==> (number_1 number_2)
             ,(* (term number_1) (term number_2)))
        with
        [(--> (a M_1) (b M_1)) (==> a b)])
       '((2 3) (4 5)))
      (list '((2 3) 20)
            '(6 (4 5))))

(let ()
  (define-language L
    (n ::= natural))
  
  (test (apply-reduction-relation
         (reduction-relation
          L
          [==> (n_1 n_2) (n_2 n_1)]
          with
          [(--> (any a) b)
           (==> a b)])
         (term (42 (1 2))))
        (list (term (2 1))))

  (test (apply-reduction-relation
         (reduction-relation
          L
          [==> (n_1 n_2) (n_2 n_1)]
          with
          [(--> (any any_1 any_2 a) b)
           (==> a b)])
         (term (blah blah blah (1 2))))
        (list (term (2 1)))))

; The scope of a `where' clause includes the left-hand sides
; of subsequent `where' clauses.
(test (apply-reduction-relation
       (reduction-relation
        grammar
        (--> any
             1
             (where number_1 2)
             (where 2 number_1)))
       'dontcare)
      '(1))

; shortcuts like this fail if compilation fails to preserve
; lexical context for side-conditions expressions.
(test (let ([x #t])
        (apply-reduction-relation
         (reduction-relation
          grammar
          (==> variable variable)
          with
          [(--> (a (side-condition number x)) b)
           (==> a b)])
         '(x 4)))
      '(x))

; test multiply matching `where' with failing `where' inside
(test (apply-reduction-relation
       (reduction-relation
        empty-language
        (--> ()
             ()
             (where (number_1 ... number_i number_i+1 ...)
                    (1 2 3))
             (where number_i 2)))
       '())
      '(()))

(test (apply-reduction-relation
       (reduction-relation
        empty-language
        (--> (in-hole (name E
                            (in-hole ((hide-hole hole) hole)
                                     hole))
                      number)
             (in-hole E ,(add1 (term number)))))
       (term (hole 2)))
      (list (term (hole 3))))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation 
        grammar
        (--> (number_1 number_2) 
             ,(* (term number_1) (term number_2))
             mul))
       '(4 5))
      (list (list "mul" 20)))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation 
        grammar
        (--> (number_1 number_2) 
             ,(* (term number_1) (term number_2))
             "mul"))
       '(4 5))
      (list (list "mul" 20)))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation 
        grammar
        (--> (number_1 number_2) 
             ,(* (term number_1) (term number_2))))
       '(4 5))
      (list (list #f 20)))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation 
        grammar
        (==> (number_1 number_2) 
             ,(* (term number_1) (term number_2))
             mult)
        with
        [(--> (M_1 a) (M_1 b)) (==> a b)])
       '((2 3) (4 5)))
      (list (list "mult" '((2 3) 20))))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation
        grammar
        (--> any
             (number_i number_i*)
             (where (number_0 ... number_i number_i+1 ...) any)
             (where (number_0* ... number_i* number_i+1* ...) any)
             pick-two
             (computed-name
              (format "(~s, ~s)"
                      (length (term (number_0 ...)))
                      (length (term (number_0* ...)))))))
       '(9 7))
      '(("(1, 1)" (7 7)) ("(1, 0)" (7 9)) ("(0, 1)" (9 7)) ("(0, 0)" (9 9))))

(test (apply-reduction-relation/tag-with-names
       (reduction-relation grammar (--> 1 2 (computed-name 3))) 1)
      '(("3" 2)))

(test (apply-reduction-relation
       (union-reduction-relations
        (reduction-relation empty-language
                            (--> x a)
                            (--> x b))
        (reduction-relation empty-language
                            (--> x c)
                            (--> x d)))
       'x)
      (list 'a 'b 'c 'd))

(test (apply-reduction-relation
       (union-reduction-relations
        (reduction-relation empty-language (--> x a))
        (reduction-relation empty-language (--> x b))
        (reduction-relation empty-language (--> x c))
        (reduction-relation empty-language (--> x d)))
       'x)
      (list 'a 'b 'c 'd))


(let ([R (reduction-relation empty-language #:domain number (--> 1 a "first"))]
      [S (reduction-relation empty-language (--> 2 a "second"))])
  (test (apply-reduction-relation (union-reduction-relations R S) 2)
        (list 'a))
  (test (apply-reduction-relation (union-reduction-relations S R) 2)
        (list 'a)))

(test (apply-reduction-relation
       (reduction-relation 
        empty-language
        (--> (number_1 number_2) 
             number_2
             (side-condition (< (term number_1) (term number_2))))
        (--> (number_1 number_2) 
             number_1
             (side-condition (< (term number_2) (term number_1)))))
       '(1 2))
      (list 2))

(test (apply-reduction-relation
       (reduction-relation 
        empty-language
        (--> x #f))
       (term x))
      (list #f))

(define-language x-language
  (x variable))

(test (apply-reduction-relation
       (reduction-relation 
        x-language
        (--> x (x x)))
       'y)
      (list '(y y)))

(test (apply-reduction-relation
       (reduction-relation 
        x-language
        (--> (x ...) ((x ...))))
       '(p q r))
      (list '((p q r))))

#;
(test (apply-reduction-relation
       (reduction-relation 
        empty-language
        #:main-arrow :->
        (:-> 1 2))
       1)
      '(2))

(test (apply-reduction-relation
       (reduction-relation 
        empty-language
        #:domain number
        (--> 1 2))
       1)
      '(2))

;; Should not have syntax error
(test (apply-reduction-relation
       (reduction-relation
        empty-language
        #:domain boolean
        (--> boolean_12 boolean_12))
       #f)
      '(#f))

(test (let ([red
             (reduction-relation 
              empty-language
              #:domain number
              (--> 1 2))])
        (with-handlers ((exn? exn-message))
          (apply-reduction-relation red 'x)
          'no-exception-raised))
      "reduction-relation: not in domain\n  term: x")

(test (let ([red
             (reduction-relation 
              empty-language
              #:domain number
              (--> 1 x))])
        (with-handlers ((exn? exn-message))
          (apply-reduction-relation red 1)
          'no-exception-raised))
      "reduction-relation: relation reduced outside its domain\n  term: x\n  via: an unnamed rule")

(let* ([red1
        (reduction-relation 
         empty-language
         #:domain (side-condition number_1 (even? (term number_1)))
         (--> number number))]
       [red2
        (reduction-relation 
         empty-language
         #:domain (side-condition number_1 (odd? (term number_1)))
         (--> number number))]
       [red-c
        (union-reduction-relations red1 red2)])
  
  ;; ensure first branch of 'union' is checked  
  (test (with-handlers ((exn? exn-message))
          (apply-reduction-relation red-c 1)
          'no-exception-raised)
        "reduction-relation: not in domain\n  term: 1")
  
  ;; ensure second branch of 'union' is checked
  (test (with-handlers ((exn? exn-message))
          (apply-reduction-relation red-c 2)
          'no-exception-raised)
        "reduction-relation: not in domain\n  term: 2"))

(let ()
  (define-language l1
    (D 0 1 2))
  (define r1
    (reduction-relation 
     l1
     #:domain D
     (--> D D)))
  (define-language l2
    (D 0 1 2 3))
  (define r2
    (extend-reduction-relation r1 l2))
  
  ;; test that the domain is re-interpreted wrt the new language
  (test (apply-reduction-relation r2 3)
        '(3)))

(let ()
  (define-language L)
  (define R
    (reduction-relation L #:domain 1 (--> any any)))
  (define S
    (extend-reduction-relation R L #:domain 2))
  
  ;; test that the new domain applies to inherited rules
  (test (apply-reduction-relation S 2)
        '(2))
  (test (with-handlers ([exn:fail? exn-message])
          (apply-reduction-relation S 1))
        #rx"not in domain"))

(let ()
  (define-language L)
  (define R
    (reduction-relation L (--> 1 1 "a")))
  (define S
    (extend-reduction-relation R L (--> 2 2 "a")))
  
  ;; test that overridden rules do not appear (twice)
  (test (reduction-relation->rule-names S)
        '(a)))

(let ()
  (define-language L)
  
  ;; test that symbol-named rules replace string-named rules
  (test (apply-reduction-relation
         (extend-reduction-relation
          (reduction-relation L (--> 1 1 "a"))
          L (--> 1 2 a))
         1)
        '(2))
  ;; and vice versa
  (test (apply-reduction-relation
         (extend-reduction-relation
          (reduction-relation L (--> 1 1 a))
          L (--> 1 2 "a"))
         1)
        '(2)))

(let ()
  (define-language l1
    (D 0 1 2))
  (define r1
    (reduction-relation 
     l1
     #:domain (D D)
     (--> (D_1 D_2) (D_2 D_1))))
  
  ;; test that duplicated identifiers in the domain contract do not have to be equal
  (test (apply-reduction-relation r1 (term (1 2)))
        (list (term (2 1)))))

;;test that #:arrow keyword works
(test (apply-reduction-relation 
       (reduction-relation 
        empty-language
        #:arrow :->
        (:-> 1 2))
       1)
      '(2))

(let ()
  (define-language n-lang
    [n number])
  (test (apply-reduction-relation
         (reduction-relation n-lang [--> any ,(length (redex-match n-lang n 1))])
         11)
        '(1)))

(let ([R (reduction-relation
          grammar
          (--> (number_1 number_2 ... (number_s ...) ...)
               yes
               (where number_1 1)
               (where (number_3 ...) ,(cdr (term (number_2 ...))))
               (where (number_3 ...) (3 4 5))
               (where (number_1 (number_s ...) ...)
                      ,(if (null? (term ((number_s ...) ...)))
                           (term (number_1))
                           (term (number_1 () (6) (7 8) (9 10 11)))))))])
  (test (apply-reduction-relation R (term (1 2 3 4 5))) '(yes))
  (test (apply-reduction-relation R (term (1 2 3 4))) '())
  (test (apply-reduction-relation R (term (0 2 3 4 5))) '())
  (test (apply-reduction-relation R (term (1 2 3 4 5 () (6) (7 8) (9 10 11)))) '(yes)))

;; expect union with duplicate names to fail
(test (with-handlers ((exn? (λ (x) 'passed)))
        (union-reduction-relations
         (reduction-relation 
          grammar
          (--> (number_1 number_2) 
               ,(* (term number_1) (term number_2))
               mult))
         (reduction-relation 
          grammar
          (--> (number_1 number_2) 
               ,(* (term number_1) (term number_2))
               mult)))
        'failed)
      'passed)

(test (with-handlers ((exn? (λ (x) 'passed)))
        (union-reduction-relations
         (union-reduction-relations
          (reduction-relation 
           grammar
           (--> (number_1 number_2) 
                ,(* (term number_1) (term number_2))
                mult))
          (reduction-relation 
           grammar
           (--> (number_1 number_2) 
                ,(* (term number_1) (term number_2))
                mult3)))
         
         (union-reduction-relations
          (reduction-relation 
           grammar
           (--> (number_1 number_2) 
                ,(* (term number_1) (term number_2))
                mult))
          (reduction-relation 
           grammar
           (--> (number_1 number_2) 
                ,(* (term number_1) (term number_2))
                mult2))))
        'passed)
      'passed)

;; sorting in this test case is so that the results come out in a predictable manner.
(test (sort
       (apply-reduction-relation
        (compatible-closure 
         (reduction-relation 
          grammar
          (--> (number_1 number_2) 
               ,(* (term number_1) (term number_2))
               mult))
         grammar
         M)
        '((2 3) (4 5)))
       (λ (x y) (string<=? (format "~s" x) (format "~s" y))))
      (list '((2 3) 20)
            '(6 (4 5))))

(test (apply-reduction-relation
       (compatible-closure 
        (reduction-relation 
         grammar
         (--> (number_1 number_2) 
              ,(* (term number_1) (term number_2))
              mult))
        grammar
        M)
       '(4 2))
      (list '8))

(let ()
  (define-language L [e ::= natural (e)][m ::= e])
  (define lc--> (reduction-relation L (--> 0 1)))
  
  (test (apply-reduction-relation
         (compatible-closure lc--> L e)
         (term (0)))
        (list (term (1))))
  
  ;; this test case illustrates that the old strategy for
  ;; turning the non-terminal aliases into new non-terminals
  ;; is bogus; this is the expected result for the the
  ;; language above, which means that we cannot compile
  ;; the non-terminal (plus alias) definition:
  ;;   [e m ::= natural (e)]
  ;; into the language above
  (test (apply-reduction-relation
         (compatible-closure lc--> L m)
         (term (0)))
        (list)))

(let ()
  
  (define-language lc
    [e m ::= natural x (λ (x) e) (e e)]
    [x ::= variable-not-otherwise-mentioned]
    #:binding-forms
    (λ (x) e #:refers-to x))
  
  (define lc-->
    (reduction-relation
     lc
     (--> ((λ (x) e) m) (substitute e x m))))
  
  (test (apply-reduction-relation (compatible-closure lc--> lc e)
                                  (term (λ (x) ((λ (y) y) 1))))
        (list (term (λ (x) 1))))
  (test (apply-reduction-relation (compatible-closure lc--> lc m)
                                  (term (λ (x) ((λ (y) y) 1))))
        (list (term (λ (x) 1)))))

(test (with-handlers ((exn:fail? exn-message))
        (apply-reduction-relation
         (context-closure 
          (reduction-relation
           empty-language #:domain #f
           (--> #f #f))
          empty-language hole)
         #t)
        "exn not raised")
      #rx"^reduction-relation:")

(test (apply-reduction-relation
       (context-closure 
        (context-closure 
         (reduction-relation grammar (--> 1 2))
         grammar
         (y hole))
        grammar
        (x hole))
       '(x (y 1)))
      (list '(x (y 2))))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (--> (variable_1 variable_2) 
             (variable_1 variable_2 x)
             mul
             (fresh x)))
       '(x x1))
      (list '(x x1 x2)))

(test (apply-reduction-relation
       (reduction-relation 
        grammar
        (~~> number 
             x
             (fresh x))
        with 
        [(--> (variable_1 variable_2 a) (variable_1 variable_2 b)) (~~> a b)])
       '(x x1 2))
      (list '(x x1 x2)))

(test (apply-reduction-relation
       (reduction-relation 
        x-language
        (--> (x_1 ...)
             (x ...)
             (fresh ((x ...) (x_1 ...)))))
       '(x y x1))
      (list '(x2 x3 x4)))

(test (apply-reduction-relation
       (reduction-relation
        empty-language
        (--> (variable_1 ...)
             (x ... variable_1 ...)
             (fresh ((x ...) (variable_1 ...) (variable_1 ...)))))
       '(x y z))
      (list '(x1 y1 z1 x y z)))

(test (apply-reduction-relation 
       (reduction-relation 
        empty-language
        (--> any (any_y x)
             (where any_y x)
             (fresh x)))
       (term junk))
      (list '(x x1)))

(test (apply-reduction-relation 
       (reduction-relation 
        empty-language
        (--> (variable ...) (variable_0 ... variable_1 ...)
             (fresh ((variable_0 ...) (variable ...)))
             (fresh ((variable_1 ...) (variable ...)))))
       (term (x y)))
      (list '(variable_0 variable_1 variable_2 variable_3)))


;; test that redex match can be used in a side-condition 
;; with the same language that is used to define the 
;; reduction relation.
(test (apply-reduction-relation
       (reduction-relation
        empty-language
        (--> any_1 3
             (side-condition (redex-match empty-language (any_1 any_2) (term any_1)))))
       '(a b))
      '(3))

(test (apply-reduction-relation
       (reduction-relation
        empty-language
        (--> variable_1
             (x variable_1)
             (fresh (x variable_1))))
       'q)
      (list '(q1 q)))

(test (apply-reduction-relation
       (extend-reduction-relation (reduction-relation empty-language (--> 1 2))
                                  empty-language
                                  (--> 1 3))
       1)
      '(3 2))

(test (apply-reduction-relation
       (extend-reduction-relation
        (reduction-relation empty-language (--> 1 2 (computed-name 1)))
        empty-language
        (--> 1 3 (computed-name 1)))
       1)
      '(3 2))

(test (apply-reduction-relation
       (extend-reduction-relation
        (reduction-relation empty-language (--> 1 2 (computed-name 1) x))
        empty-language
        (--> 1 3 (computed-name 1) x))
       1)
      '(3))

(let ()
  (define-language e1
    (e 1))
  (define-language e2
    (e 2))
  (define red1 (reduction-relation e1 (--> e (e e))))
  (define red2 (extend-reduction-relation red1 e2 (--> ignoreme ignoreme)))
  (test (apply-reduction-relation red1 1) '((1 1)))
  (test (apply-reduction-relation red1 2) '())
  (test (apply-reduction-relation red2 1) '())
  (test (apply-reduction-relation red2 2) '((2 2))))

(let ()
  (define red1 (reduction-relation empty-language
                                   (--> a (a a) 
                                        a)
                                   (--> b (b b) 
                                        b)
                                   (--> q x)))
  (define red2 (extend-reduction-relation red1
                                          empty-language
                                          (--> a (c c)
                                               a)
                                          (--> q z)))
  (test (apply-reduction-relation red1 (term a)) (list (term (a a))))
  (test (apply-reduction-relation red1 (term b)) (list (term (b b))))
  (test (apply-reduction-relation red1 (term q)) (list (term x)))
  (test (apply-reduction-relation red2 (term a)) (list (term (c c))))
  (test (apply-reduction-relation red2 (term b)) (list (term (b b))))
  (test (apply-reduction-relation red2 (term q)) (list (term z) (term x))))

(let ()
  (define red1 
    (reduction-relation
     empty-language
     (==> a (a a) 
          a)
     (==> b (b b) 
          b)
     (==> q w)
     with
     [(--> (X a) (X b)) (==> a b)]))
  
  (define red2 
    (extend-reduction-relation
     red1
     empty-language
     (==> a (c c)
          a)
     (==> q z)
     with
     [(--> (X a) (X b)) (==> a b)]))
  
  (test (apply-reduction-relation red1 (term (X a))) (list (term (X (a a)))))
  (test (apply-reduction-relation red1 (term (X b))) (list (term (X (b b)))))
  (test (apply-reduction-relation red1 (term (X q))) (list (term (X w))))
  (test (apply-reduction-relation red2 (term (X a))) (list (term (X (c c)))))
  (test (apply-reduction-relation red2 (term (X b))) (list (term (X (b b)))))
  (test (apply-reduction-relation red2 (term (X q))) (list (term (X z)) 
                                                           (term (X w)))))

(let ()
  (define-language L (M ::= number))
  (define r (reduction-relation L (--> M M (where M M))))
  (define-extended-language L1 L (M ::= string))
  (define r1 (extend-reduction-relation r L1))
  (test (apply-reduction-relation r1 "7") '("7")))

(let ()
  (define-language L (M ::= number))
  (define-extended-language L1 L (M ::= string))
  (define-judgment-form L
    #:mode (id I O)
    #:contract (id any any)
    [(id any any)])
  (define t  (reduction-relation L (--> M M (judgment-holds (id M M)))))
  (define t1 (extend-reduction-relation t L1))
  (test (apply-reduction-relation t1 "7") '("7")))

(test (reduction-relation->rule-names
       (reduction-relation
        empty-language
        (--> x y a)))
      '(a))

(test (reduction-relation->rule-names
       (reduction-relation
        empty-language
        (--> x y a)
        (--> y z b)
        (--> z w c)))
      '(a b c))

(test (reduction-relation->rule-names
       (reduction-relation
        empty-language
        (--> x y a)
        (--> y z b)
        (--> z w c)
        (--> p q z)
        (--> q r y)
        (--> r p x)))
      '(a b c z y x))

(test (reduction-relation->rule-names
       (reduction-relation
        empty-language
        (--> x y a (computed-name "x to y"))
        (--> y z (computed-name "y to z"))))
      '(a))

(test (reduction-relation->rule-names
       (extend-reduction-relation
        (reduction-relation
         empty-language
         (--> x y a)
         (--> y z b)
         (--> z w c))
        empty-language
        (--> p q z)
        (--> q r y)
        (--> r p x)))
      '(a b c z y x))

(test (reduction-relation->rule-names
       (union-reduction-relations
        (reduction-relation
         empty-language
         (--> x y a)
         (--> y z b)
         (--> z w c))
        (reduction-relation
         empty-language
         (--> p q z)
         (--> q r y)
         (--> r p x))))
      '(a b c z y x))

(let ()
  (define-judgment-form empty-language
    #:mode (R I O)
    [(R a a)]
    [(R a b)])
  (test (apply-reduction-relation
         (reduction-relation
          empty-language
          (--> a any
               (judgment-holds (R a any))))
         'a)
        '(a b)))

; a call to a metafunction that looks like a pattern variable
(let ()
  (define result 'result)
  (define-language L
    (f any))
  (define-judgment-form L
    #:mode (J O)
    [(J (f_2))])
  (define-metafunction L
    [(f_2) ,result])
  (test (judgment-holds (J any) any)
        (list result)))

(let ()
  (define-language L0 (K ::= number))
  (define r (reduction-relation L0 #:domain natural (--> 5 6)))
  (define r0 (context-closure r L0 (hole K)))
  (test (apply-reduction-relation r0  (term (5 11))) (list (term (6 11)))))

(let ()
  (define-language L0 (K ::= number))
  (define r (reduction-relation L0 #:domain 5 #:codomain 6 (--> 5 6)))
  (define r0 (context-closure r L0 (hole K)))
  (test (apply-reduction-relation r0  (term (5 11))) (list (term (6 11)))))

;; this tests that context-closure (and thus compatible-closure)
;; play along properly with way extend-reduction-relation handles
;; language extensions
(let ()
  (define-language L0 (K ::= number))
  (define r (reduction-relation L0 (--> 5 6)))
  (define r0 (context-closure r L0 (hole K)))
  (define-language L1 (K ::= string))
  (define r1 (extend-reduction-relation r0 L1))
  (test (apply-reduction-relation r1  (term (5 "14"))) (list '(6 "14"))))

(let* ([R (reduction-relation
           empty-language
           (--> any any id))]
       [c (make-coverage R)]
       [c* (make-coverage R)])
  (parameterize ([relation-coverage (list c c*)])
    (apply-reduction-relation R 4)
    (test (covered-cases c) '(("id" . 1)))
    (test (covered-cases c*) '(("id" . 1)))))

(let* ([< (λ (c d) 
            (let ([line-no (compose
                            string->number
                            second
                            (curry regexp-match #px".*:(\\d+):\\d+"))])
              (< (line-no (car c)) (line-no (car d)))))]
       [src-ok? (curry regexp-match? #px"tl-reduction-relation.(?:.+):\\d+:\\d+")]
       [sorted-counts (λ (cc) (map cdr (sort (covered-cases cc) <)))])
  (define-metafunction empty-language
    [(f 1) 1]
    [(f 2) 2])
  (define-metafunction/extension f empty-language
    [(g 3) 3])
  (define-relation empty-language
    [(R number)
     ,(even? (term number))]
    [(R number)
     ,(= 3 (term number))])
  
  (let ([fc (make-coverage f)]
        [rc (make-coverage (reduction-relation empty-language (--> any any)))])
    (parameterize ([relation-coverage (list rc fc)])
      (term (f 2))
      (test (andmap (compose src-ok? car) (covered-cases fc))
            #t)
      (test (sorted-counts fc) '(0 1))
      
      (term (f 1))
      (term (f 1))
      (test (sorted-counts fc) '(2 1))))
  
  (let ([c (make-coverage f)])
    (parameterize ([relation-coverage (list c)])
      (term (g 1))
      (test (sorted-counts c) '(1 0))))
  (let ([c (make-coverage g)])
    (parameterize ([relation-coverage (list c)])
      (term (f 1))
      (test (sorted-counts c) '(1 0 0))))
  
  ;; coverage for define-relation not working since
  ;; it was changed to compile to judgment-form
  #;
  (let ([c (make-coverage R)])
    (parameterize ([relation-coverage (list c)])
      (term (R 2))
      (term (R 3))
      (term (R 5))
      (test (sorted-counts c) '(1 1))))
  
  (let ([c (make-coverage f)]
        [c* (make-coverage f)])
    (parameterize ([relation-coverage (list c* c)])
      (term (f 1))
      (test (sorted-counts c) '(1 0))
      (test (sorted-counts c*) '(1 0)))))

(test (apply-reduction-relation
       (reduction-relation
        x-language
        (--> (x_one x_!_one x_!_one x_!_one)
             (x_one x_!_one)))
       (term (a a b c)))
      (list (term (a x_!_one))))

(test (apply-reduction-relation
       (reduction-relation
        x-language
        (--> (x_!_one ... x_!_one) odd-length-different))
       (term (a b c d)))
      (list (term odd-length-different)))

;; tests `where' clauses in reduction relation
(test (apply-reduction-relation
       (reduction-relation empty-language
                           (--> number_1 
                                any_y
                                (where any_y ,(+ 1 (term number_1)))))
       3)
      '(4))

;; tests `where' clauses scoping
(test (let ([x 5])
        (apply-reduction-relation
         (reduction-relation empty-language
                             (--> any 
                                  any_z
                                  (where any_y ,x)
                                  (where any_x 2)
                                  (where any_z ,(+ (term any_y) (term any_x)))))
         'whatever))
      '(7))

;; tests `where' clauses bind in side-conditions
(test (let ([x 'unk])
        (apply-reduction-relation
         (reduction-relation empty-language
                             (--> any 
                                  the-result
                                  (where any_y any)
                                  (side-condition (eq? (term any_y) 'whatever))))
         'whatever))
      '(the-result))

;; test that where clauses bind in side-conditions that follow
(let ([save1 #f]
      [save2 #f])
  (term-let ([any_y (term outer-y)])
            (test (begin (apply-reduction-relation
                          (reduction-relation empty-language
                                              (--> number_1 
                                                   any_y
                                                   (side-condition (set! save1 (term any_y)))
                                                   (where any_y inner-y)
                                                   (side-condition (set! save2 (term any_y)))))
                          3)
                         (list save1 save2))
                  (list 'outer-y 'inner-y))))

(test (apply-reduction-relation
       (reduction-relation empty-language
                           (--> any 
                                any_y
                                (fresh x)
                                (where any_y x)))
       'x)
      '(x1))

(test (let ([not-and
             (λ () #f)])
        (redex-match empty-language
                     (side-condition any_1 (not-and))
                     1))
      #f)

(let ()
  ;; tests where's ability to have redex patterns, not just syntax-case patterns
  (define-language var-lang [(x y z w) variable])
  
  (define red
    (reduction-relation
     var-lang
     (--> (x ...)
          (y ... z ...)
          (where (y ... w z ...) (x ...)))))
  
  (test (apply-reduction-relation red (term (a b c)))
        (list (term (a b)) (term (a c)) (term (b c)))))


(let ([r (reduction-relation
          grammar
          (->1 1 2)
          (->2 3 4)
          (->4 5 6)
          with
          [(--> (side-condition (a number) (even? (term number))) b)
           (->1 a b)]
          [(--> (XX
                 (number number)
                 (X_1 X_1)
                 (M_!_1 M_!_1)
                 (1 ..._1 1 ..._1)
                 (1 ..._!_1 1 ..._!_1))
                b)
           (->2 XX b)]
          [(--> (a 1) b)
           (->3 a b)]
          [(->3 (a 2) b)
           (->4 a b)])])
  
  ; test that names are properly bound for side-conditions in shortcuts
  (let* ([lhs (rewrite-proc-side-conditions-rewritten (first (reduction-relation-make-procs r)))]
         [proc (third lhs)]
         [name (cadar (cddadr lhs))]
         [bind (λ (n) (make-bindings (list (make-bind name n))))])
    (test (and (proc (bind 4)) (not (proc (bind 3)))) #t))
  
  ; test binder renaming
  (let ([sym-mtch? (λ (rx) (λ (s) (and (symbol? s) (regexp-match? rx (symbol->string s)))))])
    (match (rewrite-proc-side-conditions-rewritten (second (reduction-relation-make-procs r)))
      [`(3
         (,(and n1 (? (sym-mtch? #px"^number_\\d+$"))) ,n1)
         (,(and n2 (? (sym-mtch? #px"^X_1\\d+$"))) ,n2)
         (,(and m1 (? (sym-mtch? #px"^M_!_1\\d+$"))) ,m1)
         (1 ,(and ...1 (? (sym-mtch? #px"^\\.\\.\\._1\\d+$"))) 1 ,...1)
         (1 ,(and ...!1 (? (sym-mtch? #px"^\\.\\.\\._!_1\\d+$"))) 1 ,...!1))
       #t]
      [else #f]))
  
  ; test shortcut in terms of shortcut
  (test (match (rewrite-proc-side-conditions-rewritten (third (reduction-relation-make-procs r)))
          [`(list (list 5 2) 1) #t]
          [else #f])
        #t))

(let ([< (λ (c d) (string<? (car c) (car d)))])
  
  (let* ([R (reduction-relation
             empty-language
             (--> number (q ,(add1 (term number)))
                  (side-condition (odd? (term number)))
                  side-condition)
             (--> 1 4 plain)
             (==> 2 t
                  shortcut)
             with
             [(--> (q a) b)
              (==> a b)])]
         [c (make-coverage R)])
    (parameterize ([relation-coverage (list c)])
      (apply-reduction-relation R 4)
      (test (sort (covered-cases c) <)
            '(("plain" . 0) ("shortcut" . 0) ("side-condition" . 0)))
      
      (apply-reduction-relation R 3)
      (test (sort (covered-cases c) <)
            '(("plain" . 0) ("shortcut" . 0) ("side-condition" . 1)))
      
      (apply-reduction-relation* R 1)
      (test (sort (covered-cases c) <)
            '(("plain" . 1) ("shortcut" . 1) ("side-condition" . 2)))))
  
  (let ()
    (define-language L
      (e (e e)
         (delay e)
         +inf.0
         I)
      (v (delay e)
         +inf.0
         I))
    
    (define red
      (compatible-closure
       (reduction-relation
        L
        (--> (+inf.0 +inf.0) (+inf.0 +inf.0))
        (--> (I e) e))
       L
       e))
    
    (test (apply-reduction-relation* 
           red
           (term (I (delay (+inf.0 +inf.0))))
           #:stop-when (redex-match L v))
          (list (term (delay (+inf.0 +inf.0)))))
    
    (test (apply-reduction-relation* 
           red
           (term (I (delay (+inf.0 +inf.0)))))
          '())
    
    (test (apply-reduction-relation*
           red
           (term (I (I (I I))))
           #:all? #t)
          (list (term (I (I I)))
                (term (I I))
                (term I))))

  (let ()
    (define-language L)
    (define red
      (reduction-relation
       L
       #:domain (any)
       #:codomain any
       (--> (any) any)))
    (test (apply-reduction-relation* red (term (((0)))))
          (list (term 0))))
  
  (let* ([S (reduction-relation
             empty-language
             (--> 1 1 uno))]
         [S+ (extend-reduction-relation
              S empty-language
              (--> 2 2 dos))])
    (let ([c (make-coverage S+)])
      (parameterize ([relation-coverage (list c)])
        (apply-reduction-relation S (term 1))
        (test (sort (covered-cases c) <)
              '(("dos" . 0) ("uno" . 1)))))
    (let ([c (make-coverage S)])
      (parameterize ([relation-coverage (list c)])
        (apply-reduction-relation S+ (term 1))
        (test (sort (covered-cases c) <)
              '(("uno" . 1))))))
  
  (let* ([T (reduction-relation empty-language (--> any any))]
         [c (make-coverage T)])
    (parameterize ([relation-coverage (list c)])
      (apply-reduction-relation T (term q))
      (test (regexp-match? #px"tl-reduction-relation.(?:.+):\\d+:\\d+" (caar (covered-cases c)))
            #t))))

(let ()
  (define-language x-lang
    (x ::= variable))
  
  (define-judgment-form x-lang
    #:mode (type I O)
    [-------------
     (type any any)])
  
  (test (apply-reduction-relation
         (reduction-relation
          x-lang
          (--> 1 2
               (judgment-holds (type 1 1))
               (fresh x)))
         1)
        '(2)))

(let ()
  (define red
    (reduction-relation
     empty-language
     (--> any any_2
          (where/error (any_2) any))))

  (test (apply-reduction-relation red (term (1)))
        (list 1))
  (test (with-handlers ([exn:fail? exn-message])
          (apply-reduction-relation red (term 1)))
        #rx"where/error"))


(print-tests-passed 'tl-reduction-relation.rkt)
