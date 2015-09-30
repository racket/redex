#lang racket

(module+ test
  (require rackunit)
  (require redex/reduction-semantics)

  (define (all-distinct? . lst)
    (equal? lst (remove-duplicates lst)))

  (define-language lc
    (x variable-not-otherwise-mentioned)
    (expr x
          (expr expr)
          (lambda (x) expr))
    #:binding-forms
    (lambda (x) expr #:refers-to x))

  (check-match
   (redex-let* lc
               ([(lambda (x) expr) (term (lambda (x) (y (lambda (y) (y (y x))))))])
     (term (lambda (x) expr)))
   `(lambda (,x) (y (lambda (y) (y (y ,x)))))
   (all-distinct? x 'x 'y))

  ;; test that it's not just the top-level binding form that gets freshened, when we're opening
  ;; more than one.
  (check-match
   (redex-let* lc
               ([(lambda (x_1) (lambda (x_2) expr)) (term (lambda (a) (lambda (b) (a b))))])
     (term (x_1 x_2 expr)))
   `(,aa ,bb (,aa ,bb))
   (all-distinct? 'a 'b aa bb))

  ;; naively-written substitution
  ;;(should be capture-avoiding, thanks to #:binding-forms)

  (define-metafunction lc
    subst : any x any -> any
    [(subst x x any_new) any_new]
    [(subst x x_old any_new) x]
    [(subst (any ...) x_old any_new)
     ((subst any x_old any_new) ...)]
    [(subst any x_old any_new) any])


  (check-match
   (term (subst (lambda (x) (y (lambda (y) (y y)))) y (lambda (z) (z x))))
   `(lambda (,x) ((lambda (z) (z x)) (lambda (,y) (,y ,y))))
   (all-distinct? x y `x `y))

  (check-match
   (substitute lc (term (lambda (x) (y (lambda (y) (y y))))) (term y) (term (lambda (z) (z x))))
   `(lambda (,x) ((lambda (z) (z x)) (lambda (,y) (,y ,y))))
   (all-distinct? x y `x `y))


  ;; == more complex stuff ==

  (define-language big-language
   (expr (expr expr)
         (lambda (x) expr)
         (va-lambda (x ...) expr)
         (va-vb-lambda (x ...) expr ...)
         (ieie x x x expr expr)
         (let* clauses expr)
         (let3* ((x_a expr_a) (x_b expr_b) (x_c expr_c)) expr_body)
         (conjoined-lambda ((x ...) expr) ...)
         (embedded-lambda (x) (((x) expr) expr))
         (pile-o-binders x ...)
         (boring-...-bind (x x ... x))
         (natural-let* ((x expr) ...) expr)
         x
         number
         (+ expr ...))
   (clauses (cl x expr clauses)
            no-cl)
   (x variable-not-otherwise-mentioned)
   #:binding-forms
   (lambda (x) expr #:refers-to x)
   (va-lambda (x ...) expr #:refers-to (shadow x ...))
   (va-vb-lambda (x ...) expr #:refers-to (shadow x ...) ...)
   (ieie x_i x_e x_ie expr_1 #:refers-to (shadow x_ie x_i)
         expr_2 #:refers-to (shadow x_i x_ie)) #:exports (shadow x_e x_ie)
   (let* clauses expr #:refers-to clauses)
   (cl x expr clauses #:refers-to x) #:exports (shadow clauses x)
   (let3* ((x_a expr_a) (x_b expr_b #:refers-to x_a)
           (x_c expr_c #:refers-to (shadow x_b x_a)))
          expr_body #:refers-to (shadow x_c x_b x_a))
   (conjoined-lambda ((x ...) expr #:refers-to (shadow x ...)) ...)
   (embedded-lambda (x_0) (((any_1) expr_1 #:refers-to any_1) expr_0) #:refers-to x_0)
   (pile-o-binders x ...) #:exports (shadow x ...)
   (boring-...-bind (x_1 x_2 #:...bind (whatever nothing nothing) x_3))
   (natural-let* ((x expr) #:...bind (clauses x (shadow clauses x))) expr_body #:refers-to clauses)
   ;; it would be nice if this gave an error message about `x_out` or `x_in` on definition (or worked)
   #;
   (wacky-...-bind x_out ((x_in x_side x_exp expr  #:refers-to x_out )
                          #:...bind (clauses x_side (shadow x_exp clauses)))
                   expr_body #:refers-to (shadow x_in ...))
   )



  ;; a no-op, except that it triggers freshening
  (define-metafunction big-language
    freshen-all-the-way-down : any -> any
    [(freshen-all-the-way-down (any ...))
     ((freshen-all-the-way-down any) ...)]
    [(freshen-all-the-way-down any) any])

  (define-metafunction big-language
    [(bl-subst x x any_new) any_new]
    [(bl-subst (any ...) x_old any_new)
     ((bl-subst any x_old any_new) ...)]
    [(bl-subst any x_old any_new) any])

  (define-syntax-rule (destr-test orig pat (distinct-name ...))
    (check-match (term (freshen-all-the-way-down orig))
                 `pat
                 (all-distinct? distinct-name ...)))

  (define-syntax-rule (subst-test orig old-var new-val expected (distinct-name ...))
    (begin
      (check-match (substitute big-language (term orig) (term old-var) (term new-val))
                   `expected
                   (all-distinct? distinct-name ...))
      (check-match (term (bl-subst orig old-var new-val))
                   `expected
                   (all-distinct? distinct-name ...))))


  (define-syntax-rule (destr-test-lang lang orig pat (distinct-name ...))
    (begin
      (define-metafunction lang
        fatwd : any -> any
        [(fatwd (any (... ...)))
         ((fatwd any) (... ...))]
        [(fatwd any) any])

      (check-match (term (fatwd orig))
                   `pat
                   (all-distinct? distinct-name ...))))

  ;; capture-avoiding substitution

  (subst-test (lambda (x) (a (b (lambda (a) (a b)))))
              a (lambda (y) (x y))
              (lambda (,xx) ((lambda (y) (x y)) (b (lambda (,aa) (,aa b)))))
              ('a 'b 'x 'y xx aa))

  (define-syntax-rule (aeq lhs rhs)
    (alpha-equivalent? big-language (term lhs) (term rhs)))

  ;; alpha-equivalence tests

  (parameterize
   [(default-language big-language)]

   (check-equal? (aeq (lambda (x) x) (lambda (x) x)) #t)

   (check-equal? (aeq (lambda (xxxxx) xxxxx) (lambda (y) y)) #t)

   (check-equal? (aeq (lambda (x) x) (lambda (x) y)) #f)

   (check-equal? (aeq
                      (lambda (x) (lambda (y) (x y)))
                      (lambda (y) (lambda (x) (y x))))
                 #t)

   (check-equal? (aeq
                      (lambda (y) (lambda (x) (x y)))
                      (lambda (y) (lambda (x) (y x))))
                 #f)

   (check-equal? (aeq
                      (lambda (y) (lambda (a) a))
                      (lambda (y) (lambda (b) b)))
                 #t)

   (check-equal? (aeq
                      (x (lambda (x) x))
                      (y (lambda (y) y)))
                 #f)

   (check-equal? (aeq
                      (a (lambda (x) x))
                      (a (lambda (y) y)))
                 #t)

   (check-equal? (aeq
                      (va-vb-lambda (a b c) a b c d)
                      (va-vb-lambda (x y z) x y z d))
                 #t)

   (check-equal? (aeq
                      (va-vb-lambda (a b c) a b c d)
                      (va-vb-lambda (x y z) x y c d))
                 #f)

   (check-equal? (aeq a (a)) #f)

   (check-equal? (aeq (b) (a)) #f)

   (check-equal? (aeq (((a) a) a) (((b) a) a)) #f)

   (check-equal? (aeq (((a) a) a) (((a) a) a)) #t)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (aa 6)) no-cl))) (aa (bb cc))))
                 #t)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (a 6)) no-cl))) (aa (bb cc))))
                 #f)

   (check-equal? (aeq
                      (let* (cl a x (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
                      (let* (cl aa x (cl bb (aa 5) (cl cc (bb (aa 6)) no-cl))) (aa (bb c))))
                 #f)

   (check-equal? (aeq
                      ((lambda (x) x) 8)
                      ((lambda (y) y) 8))
                 #t)

   (check-equal? (aeq
                      ((lambda (x) (lambda (y) (x y))) 8)
                      ((lambda (y) (lambda (x) (x y))) 8))
                 #f)

   ;; tests for https://github.com/paulstansifer/redex/issues/10

   (check-equal? (aeq
                      (1 2 3 (cl f (lambda (x) x) no-cl))
                      (1 2 3 (cl f (lambda (y) y) no-cl)))
                 #t)

   (check-equal? (aeq
                      (1 2 3 (cl f (lambda (x) x) no-cl))
                      (1 2 3 (cl g (lambda (x) x) no-cl)))
                 #f)

   (check-equal? (aeq
                      (pile-o-binders a b c)
                      (pile-o-binders x y z))
                 #f)

   (check-equal? (aeq
                      ((pile-o-binders a b c))
                      ((pile-o-binders x y z)))
                 #f)

   (check-equal? (aeq
                  ((natural-let* ((a (+ a b c)) (b (+ a b c)) (c (+ a b c))) (+ a b c)))
                  ((natural-let* ((aa (+ a b c)) (bb (+ aa b c)) (cc (+ aa bb c))) (+ aa bb cc))))
                 #t)

   (check-equal? (aeq
                  ((natural-let* ((a (+ a b c)) (b (+ a b c)) (c (+ a b c))) (+ a b c)))
                  ((natural-let* ((aa (+ a b c)) (bb (+ aa b c)) (cc (+ aa bb cc))) (+ aa bb cc))))
                 #f)

   )
  (destr-test
   (1 2 3 (cl f (lambda (x) x) no-cl))
   (1 2 3 (cl f (lambda (,xx) ,xx) ,no-cl))
   ('f 'x xx))


  ;; TODO: the `no-cl` shouldn't be freshened. Doing proper pattern compilation
  ;; should get rid of that problem

  (destr-test
   (lambda (x) (let* (cl x 5 no-cl) x))
   (lambda (,x-outer) (let* (cl ,x-inner 5 ,no-cl) ,x-inner))
   (x-outer x-inner 'x))

  (destr-test
   (let* (cl a 4 (cl b (a 5) (cl c (b (a 6)) no-cl))) (a (b c)))
   (let* (cl ,aa 4 (cl ,bb (,aa 5) (cl ,cc (,bb (,aa 6)) ,no-cl))) (,aa (,bb ,cc)))
   ('a aa 'b bb 'c cc))

  (destr-test
   (let* (cl  a 1 (cl  a  a no-cl))  a)
   (let* (cl ,a 1 (cl ,b ,a ,no-cl)) ,b)
   (a b 'a))


  ;; test that nested structure doesn't get lost

  (destr-test
   (embedded-lambda (a) (((b) (a b)) (a b)))
   (embedded-lambda (,aa) (((,bb) (,aa ,bb)) (,aa b)))
   (aa bb 'a 'b))

  (destr-test
   (embedded-lambda (a) (((a) a) a))
   (embedded-lambda (,aa) (((,bb) ,bb) ,aa))
   (aa bb 'a))

  (destr-test
   (embedded-lambda (a) ((((cl a x no-cl)) a) a))
   (embedded-lambda (,aa) ((((cl ,bb x ,no-cl)) ,bb) ,aa))
   (aa bb 'a))


  (destr-test
   (let3* ((a 1) (b a) (c (a b)))
           (a (b c)))
   (let3* ((,aa 1) (,bb ,aa) (,cc (,aa ,bb)))
          (,aa (,bb ,cc)))
   (aa bb cc 'a 'b 'c))

  (destr-test
   (conjoined-lambda ((a b c) (a (b (c d)))) ((a b) (b a)))
   (conjoined-lambda ((,a ,b ,c) (,a (,b (,c d))))
                   ((,a2 ,b2) (,b2 ,a2)))
   (a b c a2 b2 'a 'b 'c))

  (destr-test
   (let* (cl a ((lambda (a) a) a)
             (cl x ((lambda (a) a) a) no-cl)) a)
   (let* (cl ,a1 ((lambda (,a2) ,a2) a)
             (cl ,x ((lambda (,a3) ,a3) ,a1) ,no-cl)) ,a1)
   (a1 a2 a3 'a))

  (destr-test
   (va-lambda (a b c) (+ c b a))
   (va-lambda (,a1 ,b1 ,c1) (+ ,c1 ,b1 ,a1))
   (a1 b1 c1 'a 'b 'c))

  (destr-test
   (va-lambda (a b c) (va-lambda (a b c) (+ a b c)))
   (va-lambda (,a2 ,b2 ,c2) (va-lambda (,a1 ,b1 ,c1) (+ ,a1 ,b1 ,c1)))
   (a1 b1 c1 a2 b2 c2 'a 'b 'c))

  (destr-test
   (va-vb-lambda (a b c) (+ c b a) a b c)
   (va-vb-lambda (,a1 ,b1 ,c1) (+ ,c1 ,b1 ,a1) ,a1 ,b1 ,c1)
   (a1 b1 c1 'a 'b 'c))

  ;; #:...bind tests

  (destr-test
   (boring-...-bind (a b c d e f))
   (boring-...-bind (a b c d e f))
   ())

  (destr-test
   (natural-let* ((a (+ a b c d))
                  (b (+ a b c d))
                  (c (+ a b c d))
                  (d (+ a b c d)))
      (+ a b c d))
   (natural-let* ((,a (+ a b c d))
                  (,b (+ ,a b c d))
                  (,c (+ ,a ,b c d))
                  (,d (+ ,a ,b ,c d)))
      (+ ,a ,b ,c ,d))
   (a b c d 'a 'b 'c 'd))

  (destr-test
   (natural-let* ((a
                   (natural-let* ((a (+ a b c))
                                  (b (+ a b c)))
                     (+ a b)))
                  (b (+ a b c))
                  (c (+ a b c)))
     (natural-let* ((a a)
                    (b (+ a b)))
       (+ a b c)))
   (natural-let* ((,a
                   (natural-let* ((,aa (+ a b c))
                                  (,bb (+ ,aa b c)))
                     (+ ,aa ,bb)))
                  (,b (+ ,a b c))
                  (,c (+ ,a ,b c)))
     (natural-let* ((,aaa ,a)
                    (,bbb (+ ,aaa ,b)))
       (+ ,aaa ,bbb ,c)))
   (a b c aa bb aaa bbb 'a 'b 'c))

  ;; TODO: try a form with nested `#:...bind`


  (define-judgment-form lc
    #:mode (j-subst I I I O)
    #:contract (j-subst expr x expr expr)

    [(j-subst expr_l x expr_new expr_l-res)
     (j-subst expr_r x expr_new expr_r-res)
     ----------
     (j-subst (expr_l expr_r) x expr_new (expr_l-res expr_r-res))]

    [(j-subst expr_body x expr_new expr_res) ;; note the naive-ness!
     ----------
     (j-subst (lambda (x_param) expr_body) x expr_new 
              (lambda (x_param) expr_res))]

    [----------
     (j-subst x x expr_new expr_new)]

    [(side-condition
      ,(or (not (symbol=? (term x_other) (term x)))))
     ----------
     (j-subst x_other x expr_new x_other)])

  (check-match 
   (judgment-holds (j-subst (x y) x z expr_out) expr_out)
   `((z y)))

  (check-match
   (judgment-holds (j-subst (lambda (x) (y (x (lambda (y) (x (y (lambda (z) (z (y x))))))))) 
                            y (lambda (i) (x i)) expr_out)
                   expr_out)
   `((lambda (,x) ((lambda (,i) (x ,i)) (,x (lambda (,y) (,x (,y (lambda (,z) (,z (,y ,x))))))))))
   (all-distinct? x i y z 'x))

)


;; == interactions with `extend-language` and `union-language` ==

(module+ test
  (define-language va-lc
    (x variable-not-otherwise-mentioned)
    (expr x
          (expr ...)
          (lambda (x ...) expr))
    #:binding-forms
    (lambda (x ...) expr #:refers-to (shadow x ...)))

  (define-extended-language lc-with-extra-lambda va-lc
    (expr ....
          (extra-lambda (x) expr))
    #:binding-forms
    (extra-lambda (x) expr #:refers-to x))

  (define (all-distinct-vars? . lst)
    (and (equal? lst (remove-duplicates lst))
         (andmap symbol? lst)))

  (define-syntax-rule (define-subst subst-name lang)
    (define-metafunction lang
      subst-name : any x any -> any
      [(subst-name x x any_new) any_new]
      [(subst-name x x_old any_new) x]
      [(subst-name (any (... ...)) x_old any_new)
       ((subst-name any x_old any_new) (... ...))]
      [(subst-name any x_old any_new) any]))

  (define-subst subst-lwel lc-with-extra-lambda)

  (check-match
   (term (subst-lwel (lambda (x) (extra-lambda (y) (x y z
                                                      (lambda (z) z)
                                                      (extra-lambda (z) z))))
                     z (w x y z)))
   `(lambda (,x) (extra-lambda (,y) (,x ,y (w x y z)
                                        (lambda (,z0) ,z0)
                                        (extra-lambda (,z1) ,z1))))
   (all-distinct-vars? x y z0 z1 `w `x `y `z))

  (define-language definition-lang
    (x variable-not-otherwise-mentioned)
    (block (blk stmt block)
           ())
    (stmt expr
          (def x expr))
    (expr (+ expr expr)
          number
          (x)) ;; this is to define plain variable references from being interpreted as binders
    #:binding-forms
    (def x expr) #:exports x
    (blk stmt block #:refers-to stmt))

  (destr-test-lang
   definition-lang
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))


  (define-union-language union-def-lc definition-lang lc)

  (destr-test-lang
   union-def-lc
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))

  (define-subst subst-udl union-def-lc)

  (check-match
   (term (subst-udl
          (blk (x)
               (blk (z)
                    (blk (def x (+ (lambda (z) z) (lambda (x) z)))
                         (blk (def z x)
                              (blk (z) ())))))
          z (w x y)))
   `(blk (x)
         (blk ((w x y))
              (blk (def ,x0 (+ (lambda (,z0) ,z0) (lambda (,x1) (w x y))))
                   (blk (def ,z1 ,x)
                        (blk (,z1) ())))))
   (all-distinct-vars? `w `x `y `z x0 x1 z0 z1))

  (define-union-language four-lcs (a. lc) (b. lc) lc (c. lc))

  (destr-test-lang
   four-lcs
   (lambda (a) a)
   (lambda (,aa) ,aa)
   (aa 'a))

  (define-union-language pfx-def-and-lc (def. definition-lang) (lc. lc))

  (destr-test-lang
   pfx-def-and-lc
   (lambda (a) a)
   (lambda (,aa) ,aa)
   (aa 'a))

  (destr-test-lang
   pfx-def-and-lc
   (blk (def a 1) (blk (+ (a) (a)) ()))
   (blk (def ,aa 1) (blk (+ (,aa) (,aa)) ()))
   (aa 'a))

  (define-language lc-no-binding
    (expr x
          (expr expr)
          (lambda (x) expr))
    (x variable-not-otherwise-mentioned))

  (define-extended-language lc-extended-with-binding lc-no-binding
    (expr ....)
    (x ....)
    #:binding-forms
    (lambda (x) expr #:refers-to x))

  (destr-test-lang
   lc-extended-with-binding
   (lambda (x) (lambda (y) (x y)))
   (lambda (,x) (lambda (,y) (,x ,y)))
   (x y 'x 'y))

  ;; test that judgment forms set `default-language`

  (define-judgment-form lc-extended-with-binding
    #:mode (dl-param-test-jf O)

    [(where any ,(equal? (default-language) lc-extended-with-binding))
     ----------
     (dl-param-test-jf any)])

  (check-equal? (judgment-holds (dl-param-test-jf any) any) `(#t))

  ;; ... and metafunctions

  (define-metafunction lc-extended-with-binding
    [(dl-param-test-mf)
     ,(equal? (default-language) lc-extended-with-binding)])

  (check-equal? (term (dl-param-test-mf)) #t)

 )
