(#rx"define-judgment-form:.*expression context"
 ([illegal-def (define-judgment-form L #:mode (J) [(J)])])
 (values illegal-def))

(#rx"expected an identifier defined by define-language"
 ([not-lang q])
 (define-judgment-form not-lang))

(#rx"expected.*I.*or.*O"
 ([bad-mode q])
 (define-judgment-form syn-err-lang
   #:mode (sum I bad-mode O)))

(#rx"expected mode specification"
 ([bad-spec q])
 (define-judgment-form syn-err-lang
   #:mode bad-spec))

(#rx"expected contract specification"
 ([bad-spec q])
 (define-judgment-form syn-err-lang
   #:mode (sum I I O)
   #:contract bad-spec))

(#rx"expected at most one contract specification"
 ([dup-spec (J)])
 (define-judgment-form syn-err-lang
  #:mode (J)
  #:contract (J)
  #:contract dup-spec))

(#rx"expected at most one contract specification"
 ([dup-spec1 (J)] [dup-spec2 (J)])
 (define-judgment-form syn-err-lang
   #:contract (J)
   #:mode (J)
   #:contract dup-spec1
   #:contract dup-spec2))

(#rx"expected the same name"
 ([name1 J] [name2 K]) ([name3 J])
 (define-judgment-form syn-err-lang
   #:mode (name1)
   #:contract (name2)
   [(name3)]))

(#rx"expected the same name"
 ([name1 J] [name2 K]) ([name3 J])
 (define-judgment-form syn-err-lang
   #:mode (name1)
   #:contract (name3)
   [(name2)]))

(#rx"expected at least one rule"
 ([bad-def (define-judgment-form syn-err-lang
             #:mode (J I)
             #:contract (J n))])
 bad-def)
(#rx"malformed premise"
 ([bad-prem q])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I)
     [(J number)
      bad-prem
      q])
   (void)))
(#rx"expected judgment form name"
 ([bad-judgment-form q])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I)
     [(J number)
      (bad-judgment-form)])
   (void)))
(#rx"different numbers of positions"
 ([bad-def (define-judgment-form syn-err-lang
             #:mode (J I)
             #:contract (J n n)
             [(J number)])])
 bad-def)

(#rx"unbound pattern variable"
 ([unbound number_2])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I O)
     [(J number_1 unbound)
      (J number_1 number_1)])
   (void)))
(#rx"unbound pattern variable"
 ([unbound number_2])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I O)
     [(J number_1 number_2)
      (J unbound number_1)])
   (void)))
(#rx"unbound pattern variable"
 ([unbound number_3])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I O)
     [(J number_1 number_2)
      (where number_2 unbound)])
   (void)))
(#rx"unbound pattern variable"
 ([unbound q])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (J I O)
     [(J number_1 number_2)
      (where number_2 unbound)
      (where (name q number) number_1)])
   (void)))
(#rx"J: mode specifies a unary relation but use supplied 0 terms"
 ([bad-conc (J)]) ([name J])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (name I)
     [bad-conc])
   (void)))
(#rx"J: mode specifies a unary relation but use supplied 0 terms"
 ([bad-prem (J)]) ([name J])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (name I)
     [(name number)
      bad-prem])
   (void)))
(#rx"J: mode specifies a nullary relation but use supplied 1 term"
 ([bad-prem (J a)]) ([name J])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (name)
     [(name)
      bad-prem])
   (void)))


(#rx"missing ellipsis"
 ([use any_0]) ([ellipsis ...] [def any_0])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (tmpl-depth I O)
     [(tmpl-depth (def ellipsis) any)
      (tmpl-depth use any)])
   (void)))
(#rx"same binder.*different depths"
 ([binder1 any_0] [binder2 any_0])
 ([ellipsis ...])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (pat-depth I O)
     [(pat-depth (binder1 ellipsis) ())
      (pat-depth () binder2)])
   (void)))
(#rx"too many ellipses"
 ([premise (no-ellipsis any)])
 ([binder any] [name no-ellipsis] [ellipsis ...])
 (let ()
   (define-judgment-form syn-err-lang
     #:mode (name I)
     [(name binder)
      premise ellipsis])
   (void)))

(#rx"unbound pattern variable"
 ([x f_7])
 (let ()
   (define-language L
     (f any))
   (define-judgment-form L
     #:mode (J1 O)
     [(J1 x)])
   (void)))

(#rx"unbound pattern variable"
 ([use f_2]) ([outer-def f_2] [inner-def f_2])
 (let ()
   (define-language L
     (f any))
   (define-metafunction L
     [(outer-def) ()])
   (define-judgment-form L
     #:mode (K I I O)
     [(K a any_1 x)
      (K b (use) (name inner-def any))]
     [(K b any K-b-out)])
   (void)))

(#rx"does not match original mode"
 ([J1e J1]) ([J2 J2])
 (let ()
   (define-language L)
   (define-judgment-form L
     #:mode (J1 I I O)
     [(J1 any_1 any_2 any_2)])
   (define-extended-judgment-form L J1e
     #:mode (J2 I O O)
     [(J2 any_1 17 any_1)])
   (void)))

(#rx"where expected 2 part\\(s\\), but got 3"
 ([clause (where _ 1 2)]) 
 (let ()
   (define-language L)
   (define-judgment-form L
     #:mode (T)
     [clause
      -------------
      (T)])
   (void)))
(#rx"side-condition expected 1 part\\(s\\), but got 3"
 ([clause (side-condition _ 1 2)])
 (let ()
   (define-language L)
   (define-judgment-form L
     #:mode (T)
     [clause
      -------------
      (T)])
   (void)))

(#rx"judgment form extension must extend a different judgment form"
 ([f1 f]
  [f2 f])
 (let ()
   (define-language L)
   (define-judgment-form L
     #:mode (f)
     [---
      (f)])

   (let ()
     (define-extended-judgment-form L f1
       #:mode (f2))
     (void))))

(#rx"n-hole's first argument is expected to match exactly one hole"
 ([IH (in-hole EC (! s))])
 (let ()
   (define-language L
     (e ::= (! s) N (op e e))
     (EC ::= hole (op EC e) (op v e))
     (v ::= k^ (par v v))
     (N ::= natural))
   (define-judgment-form L
     #:mode (-->& I I O O)
     [--------------------------------------
      (-->& IH E
            (in-hole EC nothing) (extend E s tt))])
   (void)))
