#lang scribble/manual

@(require "shared.rkt"
          racket/runtime-path)
@(define-runtime-path traces.png "traces.png")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "tue-mor"]{Reductions and Semantics}

@goals[

@item{extend languages with concepts needed for reduction relations}

@item{developing reduction relations}

@item{defining a semantics}

@item{testing against a language}
]

@bold{Note} These notes deal with the λβ calculus, specifically its
reduction system. 

@nested[#:style 'inset
 @tabular[#:sep @hspace[5]
          #:row-properties '(bottom-border ())
  @list[
   @list[ @t{notation}   @t{meaning} ]
   @list[ @code{x}       @t{basic notion of reduction, without properties} ]
   @list[ @code{-->x}    @t{one-step reduction, generated from @code{x}, compatible with syntactic constructions} ]
   @list[ @code{-->>x}   @t{reduction, generated from @code{-->x}, transitive here also reflexive} ]
   @list[ @code{=x}      @t{``calculus'', generated from @code{-->x}, symmetric, transitive, reflexive} ]
   ]]]


@; -----------------------------------------------------------------------------
@section{Contexts, Values}

The logical way of generating an equivalence (or reduction) relation over
terms uses through inductive inference rules that make the relation
compatible with all syntactic constructions.

An alternative and equivalent method is to introduce the notion of a
context and to use it to generate the reduction relation (or equivalence)
from the notion of reduction:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(require "common.rkt")

(define-extended-language Lambda-calculus Lambda
  (e ::= .... n)
  (n ::= natural)
  (v ::= (lambda (x ...) e))
   
  ;; a context is an expression with one hole in lieu of a sub-expression 
  (C ::=
     hole
     (e ... C e ...)
     (lambda (x_!_ ...) C)))

(define Context? (redex-match? Lambda-calculus C))

(module+ test
  (define C1 (term ((lambda (x y) x) hole 1)))
  (define C2 (term ((lambda (x y) hole) 0 1)))
  (test-equal (Context? C1) #true)
  (test-equal (Context? C2) #true))
))
@;%
Filling the hole of context with an expression yields an expression: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (define e1 (term (in-hole ,C1 1)))
  (define e2 (term (in-hole ,C2 x)))

  (test-equal (in-Lambda/n? e1) #true)
  (test-equal (in-Lambda/n? e2) #true))
))
@;%
What does filling the hole of a context with a context yield?

@; -----------------------------------------------------------------------------
@section[#:tag "Long_Tutorial_Reduction_Relations"]{Reduction Relations}

Developing a reduction relation is like developing a function. Work through
examples first. A reduction relation does not have to be a function, meaning 
it may reduce one and the same term to distinct terms. 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; the λβ calculus, reductions only 
(module+ test
  ;; does the one-step reduction reduce both β redexes? 
  (test--> -->β
           #:equiv =α/racket
           (term ((lambda (x) ((lambda (y) y) x)) z))
           (term ((lambda (x) x) z))
           (term ((lambda (y) y) z)))
                 
  ;; does the full reduction relation reduce all redexes? 
  (test-->> -->β
            (term ((lambda (x y) (x 1 y 2))
                   (lambda (a b c) a)
                   3))
            1))

(define -->β 
  (reduction-relation
   Lambda-calculus
   (--> (in-hole C ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole C (subst ([e_1 x_1] ...) e)))))
))
@;%

With @racket[traces] we can visualize reduction graphs: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(traces -->β
        (term ((lambda (x y)
                 ((lambda (f) (f (x 1 y 2)))
                  (lambda (w) 42)))
               ((lambda (x) x) (lambda (a b c) a))
               3)))
))
@;%

@centerline{@image[#:scale .5 traces.png]}

Defining the call-by-value calculus requires just a small change to the
reduction rule: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define -->βv 
  (reduction-relation
   Lambda-calculus
   (--> (in-hole C ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole C (subst ([v_1 x_1] ...) e)))))
))
@;%
Let's compare traces for the same term.  You do get the same result but
significantly fewer intermediate terms. Why? 

@; -----------------------------------------------------------------------------
@section{Semantics}

First we need a standard reduction relation. The key is to define the path to
the leftmost-outermost redex, which can again be done via contexts. Here are
the relevant definitions for the by-value reduction relation:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Standard Lambda-calculus
  (v ::= n (lambda (x ...) e))
  (E ::=
     hole
     (v ... E e ...)))

(module+ test
  (define t0
    (term
     ((lambda (x y) (x y))
      ((lambda (x) x) (lambda (x) x))
      ((lambda (x) x) 5))))
  (define t0-one-step
    (term
     ((lambda (x y) (x y))
      (lambda (x) x)
      ((lambda (x) x) 5))))

  ;; yields only one term, leftmost-outermost
  (test--> s->βv t0 t0-one-step)
  ;; but the transitive closure drives it to 5
  (test-->> s->βv t0 5))

(define s->βv
  (reduction-relation
   Standard
   (--> (in-hole E ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole E (subst ((v_1 x_1) ...) e)))))

))
@;%
Note the tests-first development of the relation. 

Now we can define the semantics function: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (test-equal (term (eval-value ,t0)) 5)
  (test-equal (term (eval-value ,t0-one-step)) 5)

  (define t1
    (term ((lambda (x) x) (lambda (x) x))))
  (test-equal (lambda? t1) #true)
  (test-equal (redex-match? Standard e t1) #true)
  (test-equal (term (eval-value ,t1)) 'closure))

(define-metafunction Standard
  eval-value : e -> v or closure 
  [(eval-value e) any_1 (where any_1 (run-value e))])

(define-metafunction Standard 
  run-value : e -> v or closure 
  [(run-value n) n]
  [(run-value v) closure]
  [(run-value e)
   (run-value e_again)
   ;; @racket[(v)] means that we expect s->βv to be a function 
   (where (e_again) ,(apply-reduction-relation s->βv (term e)))])
))
@;%
 The key is the stepper-loop, which applies the Racket function
 @racket[apply-reduction-relation] repeatedly until it yields a value. 

@; -----------------------------------------------------------------------------
@section{What are Models}

Good models of programming languages are like Newtonian models of how you
drive a car. As long as your speed is within a reasonable interval, the model
accurately predicts how your car behaves. Similarly, as long as your terms
are within a reasonable subset (the model's language), the evaluator of the
model and the evaluator of the language ought to agree. 

For Racket you set up an evaluator for the language like this: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-namespace-anchor A)
(define N (namespace-anchor->namespace A))
;; Lambda.e -> Number or 'closure or exn
(define (racket-evaluator t0)
  (define result
    (with-handlers ((exn:fail? values))
      (eval t0 N)))
  (cond
    [(number? result) result]
    [(procedure? result) (term closure)]
    [else (make-exn "hello world" (current-continuation-marks))]))
))
@;%
The details don't matter. 

So the theorem is this: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-metafunction Standard
  theorem:racket=eval-value : e -> boolean
  [(theorem:racket=eval-value e)
   ,(letrec ([rr (racket-evaluator (term e))]
             [vr (term (run-value e))])
      (cond
        [(and (exn? rr) (eq? (term stuck) vr))
         #true]
        [(exn? rr) #false]
        [(eq? (term stuck) vr) #false]
        [else (equal? vr rr)]))])
))
@;%
We formulate it as a meta-function and test it on some terms: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test  
  (test-equal (term (racket=eval-value ,t0)) #true)
  (test-equal (term (racket=eval-value ,t0-one-step)) #true)
  (test-equal (term (racket=eval-value ,t1)) #true))
))
@;%

The real test comes with random testing: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(redex-check Standard e (term (theorem:racket=eval-value e)))
))
@;%
 And now it's time to discover. 
