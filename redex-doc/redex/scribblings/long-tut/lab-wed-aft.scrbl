#lang scribble/manual

@(require "shared.rkt")

@; ---------------------------------------------------------------------------------------------------
@title[#:tag "lab-wed-aft"]{@bold{Lab} Machine Transitions}

@goals[
@item{develop the CESK machine}
]

@common[]

In addition to @seclink["common.rkt"], you also want to @racket[require]
@seclink["close.rkt"] for this lab. Furthermore, if you copy code
from @secref{wed-aft}, make sure to copy the tests and to adapt the tests
as you develop the machines.

@; -----------------------------------------------------------------------------
@section[#:tag "lwa" #:style 'unnumbered]{Exercises}

@exercise["ex:cesk"]{Equip the language with assignment statements and
@racket[void]:
@;%
@(begin
#reader scribble/comment-reader
(racketblock
(define-extended-language Assignments Lambda
  (e ::= .... n + (void) (set! x e))
  (n ::= natural))
))
@;%

Start with the CS reduction system and develop the CESK
machine, re-tracing the above machine derivation.}
