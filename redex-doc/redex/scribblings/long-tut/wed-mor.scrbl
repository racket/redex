#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "wed-mor"]{Imperative Extensions} 

@goals[

@item{revise the language for assignment statements}

@item{a standard reduction system for expression-store tuples}

@item{revise the language for raising exceptions}

@item{a general reduction system for exceptions}
]

@section{Variable Assignment}

Let's add variable assignments to our language: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Assignments Lambda
  (e ::= .... n + (void) (set! x e))
  (n ::= natural))
))
@;%
This makes it like Racket, Scheme and Lisp, but unlike ML where you can
mutate only data structure (one-slot records in SML and slots in arbitrary
records in OCaml.

For writing programs in this world, you also want blocks and local
declarations. We add a task-specific @racket[let] expression: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; (let ((x_1 x_2) ...) e_1 e_2) binds the current value of x_2 to x_1,
;; evaluates e_1, throws away its value, and finally evaluates e_2 
(define-metafunction Assignments
  let : ((x e) ...) e e -> e
  [(let ([x_lhs e_rhs] ...) e_1 e_2)
   ((lambda (x_lhs ...)
      ((lambda (x_dummy) e_2) e_1))
    e_rhs ...)
   (where (x_dummy) ,(variables-not-in (term (e_1 e_2)) '(dummy)))])
))
@;%

Here are some sample programs: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define e1
  (term
   (lambda (x)
     (lambda (y)
       (let ([tmp x])
         (set! x (+ y 1))
         tmp)))))

(define p-1 (term ((,e1 1) 2)))

(define e2
  (term
   ((lambda (x)
      (let ([tmp x])
        (set! x y)
        tmp))
    (let ([tmp-z z])
      (set! z (+ z 1))
      (let ([tmp-y y])
        (set! y tmp-z)
        tmp-y)))))

(define p-2
  (term ((lambda (y) ((lambda (z) ,e2) 1)) 2)))
))
@;%
How do they behave? 

For a @emph{standard reduction relation}, we need both evaluation contexts
@emph{and} a table that keeps track of the current value of variables:  
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Assignments-s Assignments
  (E ::= hole (v ... E e ...) (set! x E))
  (σ ::= ((x v) ...))
  (v ::= n + (void) (lambda (x ...) e)))

;; (extend σ x v) adds (x v) to σ
(define-metafunction Assignments-s
  extend : σ (x ...) (any ...) -> σ
  [(extend ((x any) ...) (x_1 ...) (any_1 ...)) ((x_1 any_1) ... (x any) ...)])

;; -----------------------------------------------------------------------------
;; (lookup Γ x) retrieves x's type from Γ
(define-metafunction Assignments-s
  lookup : any x -> any
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   ,(error 'lookup "not found: ~e in: ~e" (term x) (term any_2))])
))
@;%
 Extending this table and looking up values in it, is a routine matter by
 now. 

Here is the standard reduction relation: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define s->βs
  (reduction-relation
   Assignments-s
   #:domain (e σ)
   (--> [(in-hole E x) σ]
        [(in-hole E (lookup σ x)) σ])
   (--> [(in-hole E (set! x v)) σ]
        [(in-hole E (void)) (extend σ (x) (v))])
   (--> [(in-hole E (+ n_1 n_2)) σ]
        [(in-hole E ,(+ (term n_1) (term n_2))) σ])
   (--> [(in-hole E ((lambda (x ..._n) e) v ..._n)) σ]
        [(in-hole E e) (extend σ (x_new ...) (v ...))]
        (where (x_new ...) ,(variables-not-in (term σ) (term (x ...)))))))
))
@;%
 The question is what the corresponding calculus looks like. See
 @secref{lab-wed-mor}. 

@bold{This use of the standard reduction relation is common because most
researchers @emph{do not need} the calculus. Instead they define such a
relation and consider it a semantics.}

The semantics is a function, however, that maps programs to the final
answers and possibly extracts pieces from the store. 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (test-equal (term (eval-assignments ,p-1)) 1)
  (test-equal (term (eval-assignments ,p-2)) 2)
  (test-equal (term (eval-assignments ,p-c)) (term closure)))

(define-metafunction Assignments-s
  eval-assignments : e -> v or closure
  [(eval-assignments e) (run-assignments (e ()))])

(define-metafunction Assignments-s
  run-assignments : (e σ) -> v or closure
  [(run-assignments (n σ)) n]
  [(run-assignments (v σ)) closure]
  [(run-assignments any_1)
   (run-assignments any_again)
   (where (any_again) ,(apply-reduction-relation s->βs (term any_1)))]
  [(run-assignments any) stuck])
))
@;%

@; -----------------------------------------------------------------------------
@section{Raising Exceptions}

When non-local control operators come such as ML's exceptions come into
play, reductions become (evaluation-) context-sensitive. 

Here is a language with a simple construct for raising exceptions: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Exceptions Lambda
  (e ::= .... n + (raise e))
  (n ::= integer))
))
@;%
 @bold{History} This form of exception was actually introduced into Lisp as
 the @tt{catch} and @tt{throw} combination (contrary to some statements in
 Turing-award announcements). 

Try to figure out what these expressions ought to compute: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define c1
  (term
   ((lambda (x)
      (+ 1 (raise (+ 1 x))))
    0)))

(define c2
  (term
   (lambda (y)
     ((lambda (x)
        (+ 1 (raise (+ (raise -1) x))))
      0))))

))
@;%

A calculus of exceptions needs both arbitrary term contexts and evaluation
contexts: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Exceptions-s Exceptions
  (C ::= hole (e ... C e ...) (lambda (x ...) C) (raise C))
  (E ::= hole (v ... E e ...) (raise E)) 
  (v ::= n + (lambda (x ...) e)))
))
@;%

The key insight is that an exception-raising construct erases any
surrounding evaluation context, regardless of where it shows up: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(module+ test
  (test-->> ->βc c1 (term (raise 1)))
  (test-->> ->βc c2 (term (lambda (y) (raise -1)))))

(define ->βc
  (reduction-relation
   Exceptions-s
   (--> (in-hole C (in-hole E (raise v)))
        (in-hole C (raise v))
        (where #false ,(equal? (term E) (term hole)))
        ζ)
   (--> (in-hole C (+ n_1 n_2))
        (in-hole C ,(+ (term n_1) (term n_2)))
        +)
   (--> (in-hole C ((lambda (x_1 ..._n) e) v_1 ..._n))
        (in-hole C (subst ([v_1 x_1] ...) e))
        β_v)))

))
@;%
 The question is what a standard reduction relation for such a calculus
 looks like. See @secref{lab-wed-mor}. 
