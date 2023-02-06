#lang racket/base

#|

tests the color setting ability during a reduction sequence.

In one window, you expect to see a red and a blue snip.
as you reduce you expect to see a spectrum from blue to red

In the other window, you expect to see the currently unreducted terms in green and all others white.

Also just tests that the stepper and show-derivations work. The third window is a stepper window.
Expect the second step to split and show two steps.

|#

(require redex/reduction-semantics
         redex/gui
         racket/gui/base
         racket/class
         racket/file)

(module test racket/base)

(reduction-steps-cutoff 1)

(let ()
  
  (define (get-range term-node)
    (let loop ([node term-node])
      (let ([parents (term-node-parents node)])
        (cond
          [(null? parents) (list node)]
          [else (cons node (loop (car parents)))]))))
  
  (define (color-range-pred sexp term-node) 
    (let* ([parents (get-range term-node)]
           [max-val (car (term-node-expr (car parents)))])
      (for-each
       (λ (node)
         (let ([val (car (term-node-expr node))])
           (term-node-set-color! node
                                 (make-object color% 
                                   (floor (- 255 (* val (/ 255 max-val))))
                                   0
                                   (floor (* val (/ 255 max-val)))))))
       parents)
      (term-node-color term-node)))
  
  (define-language empty-language)
  
  (traces 
   (reduction-relation
    empty-language
    (--> (number_1 word)
         (,(+ (term number_1) 1) word)
         inc))
   '(1 word)
   #:pred color-range-pred))

(let ()
  (define-language L
    (dom ::= (number word))
    (codom ::= (number word) number))
  
  (define (last-color-pred sexp term-node)
    (if (null? (term-node-children term-node))
        "green"
        "white"))
  
  (traces (reduction-relation
           L
           #:domain dom
           #:codomain codom
           (--> (number_1 word)
                (,(+ (term number_1) 1) word)
                inc)
           (--> (number_1 word)
                (,(* (term number_1) 2) word)
                dup)
           (--> (number word)
                number
                out))
          '(1 word)
          #:pred last-color-pred))

(let ()
  (define-language L
    (sexp ::= (sexp ...) number))
  (stepper
   (reduction-relation L
    #:domain sexp
    #:codomain any
    (--> number (number) (computed-name (term (12 number 34))))
    (--> 0 zero)
    (--> (any) (any any) "not-computed"))
   0))

(let ()
  (define-language L
    (e ::= (e e) n)
    (n ::= natural))
  (define-judgment-form L
    #:mode (J I O)
    [-------
     (J n n)]

    [(J e_1 n_1) (J e_2 n_2)
     ----------------------------------------
     (J (e_1 e_2) ,(+ (term n_1) (term n_2)))])
  (show-derivations
   (build-derivations
    (J (0 ((((1 2) (3 4)) ((5 6) (7 8))) ((9 10) (11 12)))) 78))))


(let ([tmp.ps (make-temporary-file "redex-derivations-ps-test~a.ps")])
  (dynamic-wind
   void
   (λ () (derivation/ps
          (derivation '(P foo) "foo"
                      (list (derivation '(P foo) "foo" '())
                            (derivation '(P foo) "foo" '())))
          tmp.ps))
   (λ ()
     (delete-file tmp.ps))))
