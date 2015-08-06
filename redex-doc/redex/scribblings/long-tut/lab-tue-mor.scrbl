#lang scribble/manual

@(require "shared.rkt")
@(require (for-label redex/reduction-semantics))

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-tue-mor"]{@bold{Lab} Designing Reductions}

@goals[
@item{developing reductions}
@item{semantics}
]

@common[]

Also require @link["close.rkt"]{close.rkt} for the @racket[fv] function. 

You also want to copy the following definitions into your drracket:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Lambda-η Lambda
  (e ::= .... n)
  (n ::= natural)
  (C ::=
     hole
     (e ... C e ...)
     (lambda (x_!_ ...) C))
  (v ::=
     n
     (lambda (x ...) e)))

(define -->β 
  (reduction-relation
   Lambda-η
   (--> (in-hole C ((lambda (x_1 ..._n) e) e_1 ..._n))
        (in-hole C (subst ([e_1 x_1] ...) e))
        β)))

(define lambda? (redex-match? Lambda-calculus e))
))
@;%
Consider equipping the one-step reduction relation with tests. 

@; -----------------------------------------------------------------------------
@section[#:tag "ltm" #:style 'unnumbered]{Exercises}

@exercise["ex:eta"]{Develop a βη reduction relation for @racket[Lambda-η].

Find a term that contains both a β- and an η-redex. Formulate a Redex test
that validates this claim. Also use @racket[trace] to graphically validate
the claim. 

Develop the β and βη standard reduction relations. @bold{Hint} Look up
@racket[extend-reduction-relation] to save some work. 

Use the standard reduction relations to formulate a semantics for both
variants. The above test case, reformulated for the standard reduction,
@emph{must} fail. Why? @bold{Note} The semantics for βη requires some
experimentation. Justify your non-standard definition of the @racket[run]
function. 

The βη semantics is equivalent to the β variant. Formulate this theorem as
a metafunction. Use @racket[redex-check] to test your theorem.

@bold{Note} Why does it make no sense to add η to this system?}

@; -----------------------------------------------------------------------------
@exercise["ex:add-value"]{Extend the by-value language with an addition
operator.

Equip both the βv reduction system and the βv standard reduction with rules
that assign addition the usual semantics.  Finally define a semantics
functions for this language.

@bold{Hint} Your rules need to escape to Racket and use its addition
operator.}

