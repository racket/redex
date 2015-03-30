#lang racket/base

(require racket/set
         rackunit
         (only-in redex/reduction-semantics define-language ::=)
         redex/private/ambiguous)

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

(define L1-vari (build-can-match-var-ht L1))


(check-equal? L1-vari
              (make-hash (list (cons 'E #f)
                               (cons 'n #t)
                               (cons 'v #f)
                               (cons 'e (konsts (set 'λ)))
                               (cons 'x-or-w #t)
                               (cons 'x (konsts (set 'λ)))
                               (cons 'w (konsts (set 'ω)))
                               (cons 'y (prefixes (set ':)))
                               (cons 'abc-prefix (prefixes (set 'abc)))
                               (cons 'z (prefixes (set '!)))
                               (cons 'q (prefixes (set ': '!))))))

(check-equal? (overlapping-patterns?
               `(list (name e (nt e)) (name e (nt e)))
               `(list λ ((name x x)) (name e e))
               L1-vari
               L1)
              #f)
(define L1-overlapping-productions-ht (build-overlapping-productions-table L1))

(check-equal? L1-overlapping-productions-ht
              (make-hash (list (cons 'E #f)
                               (cons 'n #t)
                               (cons 'v #f)
                               (cons 'e #f)
                               (cons 'x-or-w #t)
                               (cons 'x #f)
                               (cons 'w #f)
                               (cons 'y #f)
                               (cons 'z #f)
                               (cons 'abc-prefix #f)
                               (cons 'q #t))))

(define non-terminal-ambiguous-L1 (build-ambiguous-ht L1 L1-overlapping-productions-ht))
(check-equal? non-terminal-ambiguous-L1
              (make-hash (list (cons 'E #f)
                               (cons 'n #t)
                               (cons 'v #f)
                               (cons 'e #f)
                               (cons 'x-or-w #t)
                               (cons 'x #f)
                               (cons 'w #f)
                               (cons 'y #f)
                               (cons 'z #f)
                               (cons 'abc-prefix #f)
                               (cons 'q #t))))

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

(define L2-vari (build-can-match-var-ht L2))

(check-equal? L2-vari
              (make-hash (list (cons 'e (konsts (set 'λ)))
                               (cons 'x (konsts (set 'λ))))))

(check-equal? (overlapping-patterns?
               `(list (nt e))
               `(list λ)
               L2-vari
               L2)
              #f)

(check-equal? (overlapping-patterns?
               `(list (nt e) any)
               `(list λ any)
               L2-vari
               L2)
              #f)

(check-equal? (overlapping-patterns?
               `(list (nt e) (repeat (nt e) #f #f))
               `(list λ any any)
               L2-vari
               L2)
              #f)
     
(check-equal? (overlapping-patterns? `variable `(nt w) L1-vari L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix abq) `(nt abc-prefix) L1-vari L1)
              #f)
(check-equal? (overlapping-patterns? `(variable-prefix abc) `(nt abc-prefix) L1-vari L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix abcd) `(nt abc-prefix) L1-vari L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-prefix ab) `(nt abc-prefix) L1-vari L1)
              #t)
(check-equal? (overlapping-patterns? `(variable-except elephant) `(nt e) L1-vari L1)
              #t)
(check-equal? (overlapping-patterns? `variable-not-otherwise-mentioned `(nt e) L1-vari L1)
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
