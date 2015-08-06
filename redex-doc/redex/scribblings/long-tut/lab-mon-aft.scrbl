#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-mon-aft"]{@bold{Lab} Designing Metafunctions}

@goals[
@item{developing meta-functions}
@item{discovering Redex patterns}
]

@common[]

@section[#:tag "lma" #:style 'unnumbered]{Exercises}

@exercise["ex:bv"]{Design @racket[bv]. The metafunction determines the
bound variables in a @racket[Lambda] expression. A variable @racket[x] is 
@defterm{bound in @racket[e_Lambda]} if @racket[x] occurs in a
@racket[lambda]-parameter list in e_@racket[Lambda].}

@exercise["ex:lookup"]{Design @racket[lookup]. The metafunction consumes a
variable and an @tech{environment}. It determines the leftmost expression
associated with the variable; otherwise it produces @racket[#false].

Here is the definition of @deftech{environment}: 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Env Lambda
  (e ::= .... natural)
  (env ::= ((x e) ...)))
))
@;%
 The language extension also adds numbers of the sub-language of
 expressions. 

Before you get started, make sure you can create examples of
@tech{environment}s and confirm their well-formedness.}

@exercise["ex:let"]{Develop the metafunction @racket[let], which extends
 the language with a notational shorthand, also known as syntactic sugar. 

 Once you have this metafunction, you can write expressions such as 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(term 
  (let ((x (lambda (a b c) a))
        (y (lambda (x) x)))
    (x y y y)))
))
@;%
 Like Racket's @racket[let], the function elaborates surface syntax into
 core syntax:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(term 
  ((lambda (x y) (x y y y))
   (lambda (a b c) a)
   (lambda (x) x)))
))
@;%

 Since this elaboration happens as the term is constructed, all other
 metafunctions work as expected on this extended syntax. For example,
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(term 
 (fv 
  (let ((x (lambda (a b c) a))
        (y (lambda (x) x)))
    (x y y y))))
))
@;%
 or 
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(term 
 (bv
  (let ((x (lambda (a b c) a))
        (y (lambda (x) x)))
    (x y y y))))
))
@;%
 produces the expected results. What are those?}

