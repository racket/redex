#lang scribble/manual

@(require "shared.rkt" racket/runtime-path)
@(define-runtime-path subject-reduction.png "subject-reduction.png")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "tue-aft"]{Types and Property Testing}

@goals[
@item{typed languages}
@item{developing type judgments}
@item{subject reduction}
]

@section{Types}

Here is a typed variant of the Lambda language: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-language TLambda
  (e ::=
     n
     +
     x
     (lambda ((x_!_ t) ...) e)
     (e e ...))
  (t ::=
     int
     (t ... -> t))
  (x ::= variable-not-otherwise-mentioned))

(define lambda? (redex-match? TLambda e))

(define e1
  (term (lambda ((x int) (f (int -> int))) (+ (f (f x)) (f x)))))
(define e2
  (term (lambda ((x int) (f ((int -> int) -> int))) (f x))))
(define e3
  (term (lambda ((x int) (x (int -> int))) x)))

(module+ test
  (test-equal (lambda? e1) #true)
  (test-equal (lambda? e2) #true)
  (test-equal (in-TLambda? e3) #false))
))
@;%

@; -----------------------------------------------------------------------------
@section{Developing Type Judgments}
 
Like metafunctions and reduction relations, type judgments are developed by
working out examples, formulating tests, and then articulating the judgment
rules: 

@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; (⊢ Γ e t) -- the usual type judgment for an LC language

(define-extended-language TLambda-tc TLambda
  (Γ ::= ((x t) ...)))

(module+ test
  (test-equal (judgment-holds (⊢ () ,e1 (int (int -> int) -> int))) #true)
  (test-equal (judgment-holds (⊢ () ,e2 t)) #false)
  (displayln  (judgment-holds (⊢ () ,e1 t) t))
  (displayln  (judgment-holds (⊢ () ,e2 t) t)))

(define-judgment-form TLambda-tc
  #:mode (⊢ I I O)
  #:contract (⊢ Γ e t)
  [----------------------- "number"
   (⊢ Γ n int)]

  [----------------------- "+"
   (⊢ Γ + (int int -> int))]
  
  [----------------------- "variable"
   (⊢ Γ x (lookup Γ x))]

  [(⊢ (extend Γ (x_1 t_1) ...) e t)
   ------------------------------------------------- "lambda"
   (⊢ Γ (lambda ((x_1 t_1) ...) e) (t_1 ... -> t))]

  [(⊢ Γ e_1 (t_2 ... -> t))
   (⊢ Γ e_2 t_2) ...
   ------------------------------------------------- "application"
   (⊢ Γ (e_1 e_2 ...) t)])
))
@;%

Here are the necessary auxiliary functions:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
;; (extend Γ (x t) ...) add (x t) to Γ so that x is found before other x-s
(module+ test
  (test-equal (term (extend () (x int))) (term ((x int)))))

(define-metafunction TLambda-tc
  extend : Γ (x t) ... -> Γ
  [(extend ((x_Γ t_Γ) ...) (x t) ...) ((x t) ...(x_Γ t_Γ) ...)])

;; (lookup Γ x) retrieves x's type from Γ
(module+ test
  (test-equal (term (lookup ((x int) (x (int -> int)) (y int)) x)) (term int))
  (test-equal (term (lookup ((x int) (x (int -> int)) (y int)) y)) (term int)))

(define-metafunction TLambda-tc
  lookup : Γ x -> t
  [(lookup ((x_1 t_1) ... (x t) (x_2 t_2) ...) x)
   t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2) ,(error 'lookup "not found: ~e" (term x))])
))
@;%

@; -----------------------------------------------------------------------------
@section{Subjection Reduction}

Let's say we define a truly broken (standard) reduction relation for
@racket[TLambda]: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define ->
  (reduction-relation
   TLambda
   #:domain e
   (--> e (lambda ((x int)) x))))
))
@;%

With @racket[trace], we can quickly see that paths in almost any term's
reduction graph do not preserve types: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(traces ->
      (term (((lambda ((x (int -> int))) x) (lambda ((x int)) x)) 1))
      #:pred (lambda (e) (judgment-holds (⊢ () ,e int))))
))
@;%
The @racket[#:pred] keyword argument supplies a Racket function that judges
whether the intermediate expression type checks, using our type judgment
from above. 

@centerline{@image[#:scale .66 subject-reduction.png]}

For simple ``type systems,'' @racket[redex-check] can be used to test a
true subject reduction statement:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(redex-check TLambda
             e
             (implies (judgment-holds (⊢ () e int))
                      (judgment-holds (⊢ () (eval-value e) int)))
             #:attempts 3)
))
@;%
