#lang racket/base

(require racket/set
         rackunit
         (only-in redex/reduction-semantics define-language ::= in-hole hole)
         redex/private/ambiguous
         (submod redex/private/ambiguous for-tests))

(define num-bot (num-konsts (set)))


(define-language L1
  (E (E e) hole) ;; cbn
  (e (e e) (λ (x) e) x)
  (x-or-w x w)
  (x variable-not-otherwise-mentioned)
  (w (variable-except ω))
  (y (variable-prefix :))
  (z (variable-prefix !))
  (abc-prefix (variable-prefix abc))
  (q y z)
  (n e q)
  (v (λ (x) e)))

(define L1-info (build-amb-info L1))

(check-equal? L1-info
              (make-hash
               (list
                (cons 'E (lp 'bot num-bot 'bot 'bot (list-lp (set 2) #f) #t))
                (cons 'n (lp 'variable num-bot 'bot 'bot (list-lp (set 2 3) #f) #f))
                (cons 'v (lp 'bot num-bot 'bot 'bot (list-lp (set 3) #f) #f))
                (cons 'e (lp (var-konsts (set 'λ)) num-bot 'bot 'bot (list-lp (set 2 3) #f) #f))
                (cons 'x-or-w (lp 'variable num-bot 'bot 'bot 'bot #f))
                (cons 'x (lp (var-konsts (set 'λ)) num-bot 'bot 'bot 'bot #f))
                (cons 'w (lp (var-konsts (set 'ω)) num-bot 'bot 'bot 'bot #f))
                (cons 'y (lp (prefixes+literals (set ':) (set)) num-bot 'bot 'bot 'bot #f))
                (cons 'abc-prefix (lp (prefixes+literals (set 'abc) (set)) num-bot 'bot 'bot 'bot #f))
                (cons 'z (lp (prefixes+literals (set '!) (set)) num-bot 'bot 'bot 'bot #f))
                (cons 'q (lp (prefixes+literals (set ': '!) (set)) num-bot 'bot 'bot 'bot #f)))))

(check-equal? (overlapping-patterns?
               `(list (name e (nt e)) (name e (nt e)))
               `(list λ (list (name x (nt x))) (name e (nt e)))
               L1-info
               L1)
              #f)
(define L1-overlapping-productions-ht (build-overlapping-productions-table L1))

(check-equal? L1-overlapping-productions-ht
              (make-hash (list (cons 'E #t)
                               (cons 'n #t)
                               (cons 'v #f)
                               (cons 'e #f)
                               (cons 'x-or-w #t)
                               (cons 'x #f)
                               (cons 'w #f)
                               (cons 'y #f)
                               (cons 'z #f)
                               (cons 'abc-prefix #f)
                               (cons 'q #f))))

(define non-terminal-ambiguous-L1
  (ambiguity-cache (build-ambiguous-ht L1 L1-overlapping-productions-ht)))
(check-equal? (ambiguity-cache-ht non-terminal-ambiguous-L1)
              (make-hash (list (cons 'E #t)
                               (cons 'n #t)
                               (cons 'v #f)
                               (cons 'e #f)
                               (cons 'x-or-w #t)
                               (cons 'x #f)
                               (cons 'w #f)
                               (cons 'y #f)
                               (cons 'z #f)
                               (cons 'abc-prefix #f)
                               (cons 'q #f))))

(let ()
  (define-language Foo
    (bar ::= baz variable)
    (baz ::= (foo variable ...)))
  (check-equal? (build-overlapping-productions-table Foo)
                (make-hash (list (cons 'bar #f) (cons 'baz #f)))))

(check-equal? (ambiguous-pattern? `(nt e) non-terminal-ambiguous-L1)
              #f)
(check-equal? (ambiguous-pattern? `(in-hole E e) non-terminal-ambiguous-L1)
              #t)
(check-equal? (ambiguous-pattern? `(list (repeat any #f #f)) non-terminal-ambiguous-L1)
              #f)
(check-equal? (ambiguous-pattern? `(list (repeat any #f #f)
                                         (repeat any #f #f))
                                  non-terminal-ambiguous-L1)
              #t)

(define-language L2
  (e (e e ...) (λ (x ...) e) x)
  (x variable-not-otherwise-mentioned))

(define L2-info (build-amb-info L2))

(check-equal? L2-info
              (make-hash
               (list (cons 'e (lp (var-konsts (set 'λ)) num-bot 'bot 'bot (list-lp (set) 1) #f))
                     (cons 'x (lp (var-konsts (set 'λ)) num-bot 'bot 'bot 'bot #f)))))

(check-equal? (overlapping-patterns?
               `(list (nt e))
               `(list λ)
               L2-info
               L2)
              #f)

(check-equal? (overlapping-patterns?
               `(list (nt e) any)
               `(list λ any)
               L2-info
               L2)
              #f)

(check-equal? (overlapping-patterns?
               `(list (nt e) (repeat (nt e) #f #f))
               `(list λ any any)
               L2-info
               L2)
              #f)
     
(check-equal? (overlapping-patterns? `variable `(nt w) L1-info L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix abq) `(nt abc-prefix) L1-info L1)
              #f)
(check-equal? (overlapping-patterns? `(variable-prefix abc) `(nt abc-prefix) L1-info L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix abcd) `(nt abc-prefix) L1-info L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix ab) `(nt abc-prefix) L1-info L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-except elephant) `(nt e) L1-info L1)
              #t)
(check-equal? (overlapping-patterns? `variable-not-otherwise-mentioned `(nt e) L1-info L1)
              #t)
              

(check-equal? (build-overlapping-productions-table L2)
              (make-hash (list (cons 'e #f)
                               (cons 'x #f))))

(let ()
  (define-language prefix-with-constants-lang
    [mm (variable-prefix mm)]
    [ff-or-mm ff mm]
    [m-or-mm m mm]
    [mmm-or-mm mmm mm])

  (check-equal? (build-overlapping-productions-table prefix-with-constants-lang)
                (make-hash (list (cons 'mm #f)
                                 (cons 'ff-or-mm #f)
                                 (cons 'm-or-mm #f)
                                 (cons 'mmm-or-mm #t)))))


(define-language L3
  (a ::= integer natural)
  (b ::= a 11)
  (c ::= (name x #t) 11)
  (d ::= a_!_1 123)
  (e ::= (in-hole hole 1) 1)
  (f ::= (variable-prefix ab) (variable-prefix cd))
  (g ::= (variable-prefix abc) (variable-prefix a))
  (h ::= (variable-prefix a) (variable-prefix abc))
  (i ::= (A ... B ...) (B ...))
  (j ::= (X X X ... X X) (X X X))
  (k ::= (X X X) (X X X ... X X))
  (l ::= (name x #t) (name x #f))
  (m ::= (name x #t) (name x #t))
  (n ::= (side-condition any #t) (side-condition any #t))
  (o ::= (side-condition 1 #t) (side-condition 2 #t))
  (p ::= 1 (1 2 3))
  (q ::= 1 number)
  (r ::= string 1)
  (s ::= boolean 1)
  (t ::= variable 1)
  (u ::= variable AA)
  (v ::= hole w)
  (w ::= hole (1 2 hole))
  (x ::= r string)
  (y ::= q number)
  (z ::= hole hole))

(define L3-overlapping-productions-ht (build-overlapping-productions-table L3))

(check-equal? L3-overlapping-productions-ht
              (make-hash (list (cons 'a #t)
                               (cons 'b #t)
                               (cons 'c #f)
                               (cons 'd #t)
                               (cons 'e #t)
                               (cons 'f #f)
                               (cons 'g #t)
                               (cons 'h #t)
                               (cons 'i #t)
                               (cons 'j #f)
                               (cons 'k #f)
                               (cons 'l #f)
                               (cons 'm #t)
                               (cons 'n #t)
                               (cons 'o #f)
                               (cons 'p #f)
                               (cons 'q #t)
                               (cons 'r #f)
                               (cons 's #f)
                               (cons 't #f)
                               (cons 'u #t)
                               (cons 'v #t)
                               (cons 'w #t)
                               (cons 'x #t)
                               (cons 'y #t)
                               (cons 'z #t))))

(define-language L4
  (a ::= number (name x real))
  (b ::= number a_!_1)
  (c ::= number (in-hole hole real))
  (d ::= (hide-hole (hole real)) (hide-hole (hole number)))
  (e ::= (hide-hole (1 2 3 hole)) (hide-hole (1 hole)))
  (f ::= number (side-condition any #t))
  (g ::= a (in-hole hole a))
  (h ::= (in-hole hole a) (in-hole hole a))
  (i ::= variable (variable-prefix x))
  (j ::= A B C (variable-prefix Q:))
  (l ::= 1 2 3)
  (m ::= (m) (m)))

(define L4-overlapping-productions-ht (build-overlapping-productions-table L4))

(check-equal? L4-overlapping-productions-ht
              (make-hash (list (cons 'a #t)
                               (cons 'b #t)
                               (cons 'c #t)
                               (cons 'd #t)
                               (cons 'e #f)
                               (cons 'f #t)
                               (cons 'g #t)
                               (cons 'h #t)
                               (cons 'i #t)
                               (cons 'j #f)
                               (cons 'l #f)
                               (cons 'm #t))))

(let ()
  (define-language L
    (e ::= 0)
    (f ::= 1 2 3)
    (g ::= e f)
    (h ::= natural)
    (i ::= real)
    (j ::= i e)
    (k ::= h g)
    (l ::= integer g))

  (check-equal? (build-amb-info L)
                (make-hash
                 (list
                  (cons 'l (lp 'bot `integer 'bot 'bot 'bot #f))
                  (cons 'f (lp 'bot `#s(num-konsts ,(set 1 2 3)) 'bot 'bot 'bot #f))
                  (cons 'k (lp 'bot `natural 'bot 'bot 'bot #f))
                  (cons 'i (lp 'bot `real 'bot 'bot 'bot #f))
                  (cons 'e (lp 'bot `#s(num-konsts ,(set 0)) 'bot 'bot 'bot #f))
                  (cons 'g (lp 'bot `#s(num-konsts ,(set 0 1 2 3)) 'bot 'bot 'bot #f))
                  (cons 'h (lp 'bot `natural 'bot 'bot 'bot #f))
                  (cons 'j (lp 'bot `real 'bot 'bot 'bot #f))))))


(let ()
  (define-language L
    (x ::= variable-not-otherwise-mentioned)
    (y ::= x natural))
  
  (define a (build-ambiguity-cache L))
  (check-equal? (ambiguous-pattern? `(nt y) a) #f))

(let ()
  (define-language L
    (x ::= 1 2 3 y)
    (y ::= 4 5 6))
  
  (define a (build-ambiguity-cache L))
  (check-equal? (ambiguous-pattern? `(nt x) a) #f))

(let ()
  (define-language L
    (x ::= 1 2 3)
    (y ::= 4 5 6)
    (z ::= x y))
  
  (define a (build-ambiguity-cache L))
  (check-equal? (ambiguous-pattern? `(nt z) a) #f))


(let ()
  (define-language Λc
    (e (x x)
       (x x))
    (x variable-not-otherwise-mentioned))
  (define a (build-ambiguity-cache Λc))
  (check-true (ambiguous-pattern? `(nt e) a)))

(let ()
  (define-language memo-lang
    (P (v))
    (v unit l)
    (l number))
  (check-false
   (ambiguous-pattern? `(list (repeat (name P (nt P)) #f #f))
                       (build-ambiguity-cache memo-lang))))

(let ()
  (define-language L
    (test (variable-prefix tag)
          call/cm)
    (test2 (variable-prefix tag)
           tags))
  (check-false (ambiguous-pattern? `(nt test) (build-ambiguity-cache L)))
  (check-true (ambiguous-pattern? `(nt test2) (build-ambiguity-cache L))))

(let ()
  (define-language L
    (e ::= (λ (x) e) x)
    (x ::= variable-not-otherwise-mentioned)
    (test ::= variable-not-otherwise-mentioned λ))
  (check-false (ambiguous-pattern? `(nt test) (build-ambiguity-cache L))))

(let ()
  (define-language L
    (q ::= a b (variable-prefix c:))
    (r ::= q d)
    (s ::= q c:d))
  (check-false (ambiguous-pattern? `(nt r) (build-ambiguity-cache L)))
  (check-true (ambiguous-pattern? `(nt s) (build-ambiguity-cache L))))

(let ()
  (define-language L
    (v #t pt)
    (pt (variable-prefix tag))

    (s1 "a" "b" "c" "d")
    (s2 "e" "f" "g" "h")
    (s3 s1 "p" "q" "r")
    (s4 s1 s2)
    (s5 s1 "a"))
  (check-false (ambiguous-pattern? `(nt v) (build-ambiguity-cache L)))
  (check-false (ambiguous-pattern? `(nt s3) (build-ambiguity-cache L)))
  (check-false (ambiguous-pattern? `(nt s4) (build-ambiguity-cache L)))
  (check-true (ambiguous-pattern? `(nt s5) (build-ambiguity-cache L))))

(let ()
  (define-language L
    (a (variable-prefix a))
    (b (variable-prefix b))
    (ab (variable-prefix ab))

    (v a aaaaaaa)
    (w a baaaaaa)
    (x a b)
    (y ab a)
    (z ab b))

  (check-true (ambiguous-pattern? `(nt v) (build-ambiguity-cache L)))
  (check-false (ambiguous-pattern? `(nt w) (build-ambiguity-cache L)))
  (check-false (ambiguous-pattern? `(nt x) (build-ambiguity-cache L)))
  (check-true (ambiguous-pattern? `(nt y) (build-ambiguity-cache L)))
  (check-false (ambiguous-pattern? `(nt z) (build-ambiguity-cache L))))


(let ()
  (define-language abort-core-lang/unambiguous
    (v pt
       (cons v v))

    (pt (variable-prefix tag)
        (PG ctc ctc v l l l)))

  (check-false (ambiguous-pattern? `(nt v) (build-ambiguity-cache abort-core-lang/unambiguous))))